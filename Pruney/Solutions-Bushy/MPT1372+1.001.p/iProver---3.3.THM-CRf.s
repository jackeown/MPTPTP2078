%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:34 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   32 (  50 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 176 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v8_struct_0(X0) )
       => ( v1_compts_1(X0)
          & v2_pre_topc(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
        & v2_pre_topc(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_pre_topc(X0)
      | ~ v8_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v8_struct_0(X0) )
     => ~ v1_finset_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_finset_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v8_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_finset_1(u1_struct_0(X0))
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ( v1_finset_1(u1_struct_0(X0))
         => v1_compts_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v1_compts_1(X0)
      & v1_finset_1(u1_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0] :
        ( ~ v1_compts_1(X0)
        & v1_finset_1(u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ v1_compts_1(sK0)
      & v1_finset_1(u1_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ v1_compts_1(sK0)
    & v1_finset_1(u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,(
    ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    v1_finset_1(u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v8_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | v1_compts_1(X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_20,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v8_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_16,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ v1_finset_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v8_struct_0(X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_13,plain,
    ( ~ v1_finset_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v8_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,negated_conjecture,
    ( ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( v1_finset_1(u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20,c_16,c_13,c_4,c_5,c_6,c_7])).


%------------------------------------------------------------------------------
