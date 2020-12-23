%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1142+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:00 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 400 expanded)
%              Number of clauses        :   81 ( 112 expanded)
%              Number of leaves         :   11 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :  530 (3656 expanded)
%              Number of equality atoms :   99 ( 145 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_orders_2(X0,X1,X3)
          & ( ( r2_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X2) )
            | ( r1_orders_2(X0,X2,X3)
              & r2_orders_2(X0,X1,X2) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK3)
        & ( ( r2_orders_2(X0,X2,sK3)
            & r1_orders_2(X0,X1,X2) )
          | ( r1_orders_2(X0,X2,sK3)
            & r2_orders_2(X0,X1,X2) ) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(X0,X1,X3)
              & ( ( r2_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2) )
                | ( r1_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_orders_2(X0,X1,X3)
            & ( ( r2_orders_2(X0,sK2,X3)
                & r1_orders_2(X0,X1,sK2) )
              | ( r1_orders_2(X0,sK2,X3)
                & r2_orders_2(X0,X1,sK2) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(X0,sK1,X3)
                & ( ( r2_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK1,X2) )
                  | ( r1_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,sK1,X2) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & ( ( r2_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( r1_orders_2(sK0,X2,X3)
                      & r2_orders_2(sK0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & ( ( r2_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( r1_orders_2(sK0,sK2,sK3)
        & r2_orders_2(sK0,sK1,sK2) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18,f17,f16,f15])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f21])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_15,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_199,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_200,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X2)
    | r1_orders_2(sK0,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_13,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X2)
    | ~ r1_orders_2(sK0,X1,X2)
    | ~ r1_orders_2(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_13])).

cnf(c_203,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X2,X0)
    | r1_orders_2(sK0,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_388,plain,
    ( ~ r1_orders_2(sK0,X0_40,X1_40)
    | ~ r1_orders_2(sK0,X2_40,X0_40)
    | r1_orders_2(sK0,X2_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X2_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_761,plain,
    ( ~ r1_orders_2(sK0,X0_40,sK2)
    | r1_orders_2(sK0,X0_40,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_1063,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_401,plain,
    ( ~ r2_orders_2(X0_39,X0_40,X1_40)
    | r2_orders_2(X0_39,X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_1026,plain,
    ( r2_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,X2_40,sK3)
    | X0_40 != X2_40
    | X1_40 != sK3 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_1028,plain,
    ( r2_orders_2(sK0,sK2,sK2)
    | ~ r2_orders_2(sK0,sK2,sK3)
    | sK2 != sK2
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_232,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_233,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_387,plain,
    ( r1_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,X0_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_1021,plain,
    ( r1_orders_2(sK0,X0_40,sK3)
    | ~ r2_orders_2(sK0,X0_40,sK3)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_1023,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_6,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_396,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_645,plain,
    ( r1_orders_2(sK0,sK2,sK3) = iProver_top
    | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_166,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_167,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ r1_orders_2(sK0,X0,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_167,c_13])).

cnf(c_172,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_171])).

cnf(c_389,plain,
    ( ~ r1_orders_2(sK0,X0_40,X1_40)
    | ~ r1_orders_2(sK0,X1_40,X0_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0))
    | X0_40 = X1_40 ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_652,plain,
    ( X0_40 = X1_40
    | r1_orders_2(sK0,X0_40,X1_40) != iProver_top
    | r1_orders_2(sK0,X1_40,X0_40) != iProver_top
    | m1_subset_1(X1_40,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_936,plain,
    ( sK2 = sK3
    | r1_orders_2(sK0,sK3,sK2) != iProver_top
    | r2_orders_2(sK0,sK2,sK3) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_652])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_21,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,negated_conjecture,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_24,plain,
    ( r2_orders_2(sK0,sK2,sK3) = iProver_top
    | r2_orders_2(sK0,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25,plain,
    ( r1_orders_2(sK0,sK2,sK3) = iProver_top
    | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,negated_conjecture,
    ( ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,plain,
    ( r2_orders_2(sK0,sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_399,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_819,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_773,plain,
    ( r2_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | X1_40 != sK2
    | X0_40 != sK1 ),
    inference(instantiation,[status(thm)],[c_401])).

cnf(c_818,plain,
    ( r2_orders_2(sK0,sK1,X0_40)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | X0_40 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_853,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK3)
    | sK3 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_854,plain,
    ( sK3 != sK2
    | sK1 != sK1
    | r2_orders_2(sK0,sK1,sK2) != iProver_top
    | r2_orders_2(sK0,sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_262,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_263,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_385,plain,
    ( ~ r1_orders_2(sK0,X0_40,X1_40)
    | r2_orders_2(sK0,X0_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0))
    | X1_40 = X0_40 ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_906,plain,
    ( ~ r1_orders_2(sK0,X0_40,sK3)
    | r2_orders_2(sK0,X0_40,sK3)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK3 = X0_40 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_907,plain,
    ( sK3 = X0_40
    | r1_orders_2(sK0,X0_40,sK3) != iProver_top
    | r2_orders_2(sK0,X0_40,sK3) = iProver_top
    | m1_subset_1(X0_40,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_909,plain,
    ( sK3 = sK2
    | r1_orders_2(sK0,sK2,sK3) != iProver_top
    | r2_orders_2(sK0,sK2,sK3) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_999,plain,
    ( r2_orders_2(sK0,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_20,c_21,c_24,c_25,c_26,c_819,c_854,c_909])).

cnf(c_1001,plain,
    ( r2_orders_2(sK0,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_999])).

cnf(c_402,plain,
    ( ~ r1_orders_2(X0_39,X0_40,X1_40)
    | r1_orders_2(X0_39,X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_788,plain,
    ( r1_orders_2(sK0,X0_40,X1_40)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | X1_40 != sK2
    | X0_40 != sK1 ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_969,plain,
    ( r1_orders_2(sK0,sK3,X0_40)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | X0_40 != sK2
    | sK3 != sK1 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_976,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | sK2 != sK2
    | sK3 != sK1 ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_8,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_394,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_647,plain,
    ( r1_orders_2(sK0,sK2,sK3) = iProver_top
    | r1_orders_2(sK0,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,plain,
    ( r1_orders_2(sK0,sK1,sK2) = iProver_top
    | r2_orders_2(sK0,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_754,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_755,plain,
    ( r1_orders_2(sK0,sK1,sK2) = iProver_top
    | r2_orders_2(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_925,plain,
    ( r1_orders_2(sK0,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_19,c_20,c_22,c_755])).

cnf(c_927,plain,
    ( r1_orders_2(sK0,sK1,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_925])).

cnf(c_808,plain,
    ( ~ r1_orders_2(sK0,sK1,X0_40)
    | r2_orders_2(sK0,sK1,X0_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | X0_40 = sK1 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_885,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r2_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK3 = sK1 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_829,plain,
    ( ~ r1_orders_2(sK0,X0_40,sK3)
    | ~ r1_orders_2(sK0,sK3,X0_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | X0_40 = sK3 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_831,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_250,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_251,plain,
    ( ~ r2_orders_2(sK0,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_386,plain,
    ( ~ r2_orders_2(sK0,X0_40,X0_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_251])).

cnf(c_423,plain,
    ( ~ r2_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_408,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1063,c_1028,c_1023,c_1001,c_976,c_927,c_885,c_831,c_423,c_408,c_5,c_10,c_11,c_12])).


%------------------------------------------------------------------------------
