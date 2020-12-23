%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1236+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 54.80s
% Output     : CNFRefutation 54.80s
% Verified   : 
% Statistics : Number of formulae       :   32 (  55 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 116 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2269,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f160])).

fof(f6821,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2269])).

fof(f2115,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2116,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f2115])).

fof(f4712,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2116])).

fof(f6610,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK770) != k1_tops_1(sK770,k1_struct_0(sK770))
      & l1_pre_topc(sK770) ) ),
    introduced(choice_axiom,[])).

fof(f6611,plain,
    ( k1_struct_0(sK770) != k1_tops_1(sK770,k1_struct_0(sK770))
    & l1_pre_topc(sK770) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK770])],[f4712,f6610])).

fof(f10770,plain,(
    k1_struct_0(sK770) != k1_tops_1(sK770,k1_struct_0(sK770)) ),
    inference(cnf_transformation,[],[f6611])).

fof(f10769,plain,(
    l1_pre_topc(sK770) ),
    inference(cnf_transformation,[],[f6611])).

fof(f2095,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4677,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2095])).

fof(f10742,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4677])).

fof(f1797,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4158,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1797])).

fof(f10137,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4158])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4141,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f10122,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4141])).

cnf(c_208,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f6821])).

cnf(c_4129,negated_conjecture,
    ( k1_struct_0(sK770) != k1_tops_1(sK770,k1_struct_0(sK770)) ),
    inference(cnf_transformation,[],[f10770])).

cnf(c_160649,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK770,k1_struct_0(sK770)))
    | ~ v1_xboole_0(k1_struct_0(sK770)) ),
    inference(resolution,[status(thm)],[c_208,c_4129])).

cnf(c_4130,negated_conjecture,
    ( l1_pre_topc(sK770) ),
    inference(cnf_transformation,[],[f10769])).

cnf(c_4102,plain,
    ( ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f10742])).

cnf(c_158772,plain,
    ( ~ l1_pre_topc(sK770)
    | v1_xboole_0(k1_tops_1(sK770,k1_struct_0(sK770))) ),
    inference(instantiation,[status(thm)],[c_4102])).

cnf(c_158810,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK770,k1_struct_0(sK770)))
    | ~ v1_xboole_0(k1_struct_0(sK770))
    | k1_struct_0(sK770) = k1_tops_1(sK770,k1_struct_0(sK770)) ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_160652,plain,
    ( ~ v1_xboole_0(k1_struct_0(sK770)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_160649,c_4130,c_4129,c_158772,c_158810])).

cnf(c_3498,plain,
    ( ~ l1_struct_0(X0)
    | v1_xboole_0(k1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f10137])).

cnf(c_160693,plain,
    ( ~ l1_struct_0(sK770) ),
    inference(resolution,[status(thm)],[c_160652,c_3498])).

cnf(c_3483,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f10122])).

cnf(c_158620,plain,
    ( l1_struct_0(sK770)
    | ~ l1_pre_topc(sK770) ),
    inference(instantiation,[status(thm)],[c_3483])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_160693,c_158620,c_4130])).

%------------------------------------------------------------------------------
