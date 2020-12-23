%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1139+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 155 expanded)
%              Number of clauses        :   28 (  36 expanded)
%              Number of leaves         :    6 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  229 ( 878 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(flattening,[],[f6])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,conjecture,(
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

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( r2_orders_2(X0,X2,X1)
                    & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_orders_2(X0,X2,X1)
          & r2_orders_2(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_orders_2(X0,sK2,X1)
        & r2_orders_2(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(X0,X2,X1)
              & r2_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( r2_orders_2(X0,X2,sK1)
            & r2_orders_2(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_orders_2(sK0,X2,X1)
              & r2_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14,f13,f12])).

fof(f20,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    r2_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f5,plain,(
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

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,negated_conjecture,
    ( v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_106,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_107,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_106])).

cnf(c_8,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ r1_orders_2(sK0,X0,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_107,c_8])).

cnf(c_112,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_281,plain,
    ( ~ r1_orders_2(sK0,X0_38,X1_38)
    | ~ r1_orders_2(sK0,X1_38,X0_38)
    | ~ m1_subset_1(X1_38,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_38,u1_struct_0(sK0))
    | X0_38 = X1_38 ),
    inference(subtyping,[status(esa)],[c_112])).

cnf(c_426,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_4,negated_conjecture,
    ( r2_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_157,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_158,plain,
    ( ~ r2_orders_2(sK0,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_158])).

cnf(c_215,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 != sK1 ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_217,plain,
    ( sK2 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_215,c_7])).

cnf(c_279,plain,
    ( sK2 != sK1 ),
    inference(subtyping,[status(esa)],[c_217])).

cnf(c_5,negated_conjecture,
    ( r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_139,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_140,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_139])).

cnf(c_222,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_140])).

cnf(c_223,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_203,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X1
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_140])).

cnf(c_204,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_426,c_279,c_223,c_204,c_6,c_7])).


%------------------------------------------------------------------------------
