%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1140+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:59 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 208 expanded)
%              Number of clauses        :   46 (  55 expanded)
%              Number of leaves         :   11 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  376 (1584 expanded)
%              Number of equality atoms :   36 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                   => ( ( r2_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
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
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
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
          & r2_orders_2(X0,X2,X3)
          & r2_orders_2(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK3)
        & r2_orders_2(X0,X2,sK3)
        & r2_orders_2(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(X0,X1,X3)
              & r2_orders_2(X0,X2,X3)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_orders_2(X0,X1,X3)
            & r2_orders_2(X0,sK2,X3)
            & r2_orders_2(X0,X1,sK2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(X0,sK1,X3)
                & r2_orders_2(X0,X2,X3)
                & r2_orders_2(X0,sK1,X2)
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
                    & r2_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,X1,X2)
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
                  & r2_orders_2(sK0,X2,X3)
                  & r2_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & r2_orders_2(sK0,sK2,sK3)
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f18,f17,f16,f15])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_11,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_229,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_230,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_338,plain,
    ( ~ r1_orders_2(sK0,X0_40,X1_40)
    | r2_orders_2(sK0,X0_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0))
    | X1_40 = X0_40 ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_758,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r2_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK3 = sK1 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_351,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_718,plain,
    ( X0_40 != X1_40
    | X0_40 = sK3
    | sK3 != X1_40 ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_719,plain,
    ( sK3 != sK1
    | sK1 = sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_350,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_689,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_352,plain,
    ( ~ r2_orders_2(X0_39,X0_40,X1_40)
    | r2_orders_2(X0_39,X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_656,plain,
    ( r2_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,sK2,sK3)
    | X0_40 != sK2
    | X1_40 != sK3 ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_688,plain,
    ( r2_orders_2(sK0,sK2,X0_40)
    | ~ r2_orders_2(sK0,sK2,sK3)
    | X0_40 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_691,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK1)
    | sK2 != sK2
    | sK1 != sK3 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_170,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_171,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X2,X0)
    | r1_orders_2(sK0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_173,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r1_orders_2(sK0,X2,X1)
    | ~ r1_orders_2(sK0,X2,X0)
    | ~ r1_orders_2(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_171,c_11])).

cnf(c_174,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X2,X0)
    | r1_orders_2(sK0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_341,plain,
    ( ~ r1_orders_2(sK0,X0_40,X1_40)
    | ~ r1_orders_2(sK0,X2_40,X0_40)
    | r1_orders_2(sK0,X2_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X2_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_174])).

cnf(c_666,plain,
    ( ~ r1_orders_2(sK0,X0_40,sK2)
    | r1_orders_2(sK0,X0_40,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_668,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_4,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_143,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_12])).

cnf(c_144,plain,
    ( ~ r2_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_143])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,X1,X0)
    | ~ r2_orders_2(sK0,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_144,c_11])).

cnf(c_147,plain,
    ( ~ r2_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_342,plain,
    ( ~ r2_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,X1_40,X0_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_147])).

cnf(c_640,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_203,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_204,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_340,plain,
    ( r1_orders_2(sK0,X0_40,X1_40)
    | ~ r2_orders_2(sK0,X0_40,X1_40)
    | ~ m1_subset_1(X0_40,u1_struct_0(sK0))
    | ~ m1_subset_1(X1_40,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_634,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_631,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_340])).

cnf(c_357,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_5,negated_conjecture,
    ( ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,negated_conjecture,
    ( r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,negated_conjecture,
    ( r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_758,c_719,c_689,c_691,c_668,c_640,c_634,c_631,c_357,c_5,c_6,c_7,c_8,c_9,c_10])).


%------------------------------------------------------------------------------
