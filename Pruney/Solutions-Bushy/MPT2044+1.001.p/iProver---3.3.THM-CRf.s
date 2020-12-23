%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 540 expanded)
%              Number of clauses        :   51 ( 115 expanded)
%              Number of leaves         :    7 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  358 (3518 expanded)
%              Number of equality atoms :   80 ( 184 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r2_hidden(X2,k1_yellow19(X0,X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
     => ( ( ~ m1_connsp_2(sK3,X0,X1)
          | ~ r2_hidden(sK3,k1_yellow19(X0,X1)) )
        & ( m1_connsp_2(sK3,X0,X1)
          | r2_hidden(sK3,k1_yellow19(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,X0,sK2)
              | ~ r2_hidden(X2,k1_yellow19(X0,sK2)) )
            & ( m1_connsp_2(X2,X0,sK2)
              | r2_hidden(X2,k1_yellow19(X0,sK2)) ) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK1,X1)
                | ~ r2_hidden(X2,k1_yellow19(sK1,X1)) )
              & ( m1_connsp_2(X2,sK1,X1)
                | r2_hidden(X2,k1_yellow19(sK1,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ m1_connsp_2(sK3,sK1,sK2)
      | ~ r2_hidden(sK3,k1_yellow19(sK1,sK2)) )
    & ( m1_connsp_2(sK3,sK1,sK2)
      | r2_hidden(sK3,k1_yellow19(sK1,sK2)) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f29,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X3] :
              ( X0 = X3
              & m1_connsp_2(X3,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X4] :
              ( X0 = X4
              & m1_connsp_2(X4,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( X0 = X4
          & m1_connsp_2(X4,X1,X2) )
     => ( sK0(X0,X1,X2) = X0
        & m1_connsp_2(sK0(X0,X1,X2),X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ( sK0(X0,X1,X2) = X0
            & m1_connsp_2(sK0(X0,X1,X2),X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | X0 != X3
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow19(X1,X2))
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X1,X2)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( sK0(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,negated_conjecture,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_70,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | ~ r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_205,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_206,plain,
    ( ~ m1_connsp_2(X0,X1,sK2)
    | r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_7,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_267,plain,
    ( ~ m1_connsp_2(X0,X1,sK2)
    | r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_206,c_7])).

cnf(c_268,plain,
    ( ~ m1_connsp_2(X0,sK1,sK2)
    | r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_9,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_272,plain,
    ( ~ m1_connsp_2(X0,sK1,sK2)
    | r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_9,c_8])).

cnf(c_455,plain,
    ( ~ m1_connsp_2(X0,sK1,sK2)
    | ~ m1_connsp_2(sK3,sK1,sK2)
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_70,c_272])).

cnf(c_456,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2)
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_5,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_72,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | r2_hidden(sK3,k1_yellow19(sK1,sK2)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( m1_connsp_2(sK0(X0,X1,X2),X1,X2)
    | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_157,plain,
    ( m1_connsp_2(sK0(X0,X1,X2),X1,X2)
    | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_158,plain,
    ( m1_connsp_2(sK0(X0,X1,sK2),X1,sK2)
    | ~ r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_309,plain,
    ( m1_connsp_2(sK0(X0,X1,sK2),X1,sK2)
    | ~ r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_158,c_7])).

cnf(c_310,plain,
    ( m1_connsp_2(sK0(X0,sK1,sK2),sK1,sK2)
    | ~ r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_314,plain,
    ( m1_connsp_2(sK0(X0,sK1,sK2),sK1,sK2)
    | ~ r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_9,c_8])).

cnf(c_429,plain,
    ( m1_connsp_2(sK0(X0,sK1,sK2),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2)
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_72,c_314])).

cnf(c_430,plain,
    ( m1_connsp_2(sK0(sK3,sK1,sK2),sK1,sK2)
    | m1_connsp_2(sK3,sK1,sK2)
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_464,plain,
    ( m1_connsp_2(sK0(sK3,sK1,sK2),sK1,sK2)
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_456,c_430])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | a_2_0_yellow19(X1,X0) = k1_yellow19(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_136,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | a_2_0_yellow19(X0,X1) = k1_yellow19(X0,X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_137,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | a_2_0_yellow19(X0,sK2) = k1_yellow19(X0,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_136])).

cnf(c_256,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | a_2_0_yellow19(X0,sK2) = k1_yellow19(X0,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_7])).

cnf(c_257,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | a_2_0_yellow19(sK1,sK2) = k1_yellow19(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_259,plain,
    ( a_2_0_yellow19(sK1,sK2) = k1_yellow19(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_9,c_8])).

cnf(c_498,plain,
    ( a_2_0_yellow19(sK1,sK2) = k1_yellow19(sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_259])).

cnf(c_521,plain,
    ( m1_connsp_2(sK0(sK3,sK1,sK2),sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_498])).

cnf(c_538,plain,
    ( m1_connsp_2(sK0(sK3,sK1,sK2),sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_521])).

cnf(c_632,plain,
    ( m1_connsp_2(sK0(sK3,sK1,sK2),sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_181,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X0,X1,X2) = X0
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X0,X1,sK2) = X0
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_288,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(X1,sK2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | sK0(X0,X1,sK2) = X0
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_7])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | sK0(X0,sK1,sK2) = X0
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,a_2_0_yellow19(sK1,sK2))
    | sK0(X0,sK1,sK2) = X0
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_9,c_8])).

cnf(c_442,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | sK0(X0,sK1,sK2) = X0
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_72,c_293])).

cnf(c_443,plain,
    ( m1_connsp_2(sK3,sK1,sK2)
    | sK0(sK3,sK1,sK2) = sK3
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_463,plain,
    ( sK0(sK3,sK1,sK2) = sK3
    | a_2_0_yellow19(sK1,sK2) != k1_yellow19(sK1,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_456,c_443])).

cnf(c_518,plain,
    ( sK0(sK3,sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_498])).

cnf(c_539,plain,
    ( sK0(sK3,sK1,sK2) = sK3 ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_639,plain,
    ( m1_connsp_2(sK3,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_632,c_539])).

cnf(c_512,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_498])).

cnf(c_540,plain,
    ( ~ m1_connsp_2(sK3,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_631,plain,
    ( m1_connsp_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_641,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_639,c_631])).


%------------------------------------------------------------------------------
