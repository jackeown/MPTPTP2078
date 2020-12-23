%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1615+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:59 EST 2020

% Result     : Theorem 0.66s
% Output     : CNFRefutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   39 (  79 expanded)
%              Number of clauses        :   18 (  24 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   16
%              Number of atoms          :   91 ( 220 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f21,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_3,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_102,negated_conjecture,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_1,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_62,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_63,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_62])).

cnf(c_5,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_65,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63,c_5])).

cnf(c_85,plain,
    ( ~ v1_xboole_0(X0)
    | u1_pre_topc(sK0) != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_65])).

cnf(c_86,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_0,plain,
    ( ~ r2_hidden(k1_xboole_0,X0)
    | v1_xboole_0(X0)
    | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_75,plain,
    ( v1_xboole_0(X0)
    | u1_pre_topc(sK0) != X0
    | k3_yellow_0(k2_yellow_1(X0)) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_65])).

cnf(c_76,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_75])).

cnf(c_91,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_86,c_76])).

cnf(c_101,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_91])).

cnf(c_106,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_102,c_101])).

cnf(c_107,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_106])).


%------------------------------------------------------------------------------
