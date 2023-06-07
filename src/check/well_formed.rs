use crate::check::ordered_env::OrderedEnv;
use crate::check::Type;

pub enum WFErr {}

pub fn well_formed(typ: Type, env: OrderedEnv) -> Result<(), WFErr> {
    match typ {
        Type::Monotype(typ) => todo!(),
        Type::Func(arg_types, res_type) => todo!(),
        _ => todo!(),
    }
}
