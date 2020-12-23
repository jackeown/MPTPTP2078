%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:13 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  79 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f259,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f99])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f156])).

fof(f228,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f157])).

fof(f293,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f228])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f242,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f230,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f157])).

fof(f53,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f53])).

fof(f105,plain,(
    ? [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f54])).

fof(f162,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) != X0
   => k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)) != sK15 ),
    introduced(choice_axiom,[])).

fof(f163,plain,(
    k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)) != sK15 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f105,f162])).

fof(f250,plain,(
    k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)) != sK15 ),
    inference(cnf_transformation,[],[f163])).

cnf(c_93,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f259])).

cnf(c_4580,plain,
    ( r1_tarski(sK15,k2_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_78,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f244])).

cnf(c_4350,plain,
    ( r1_tarski(sK15,k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)))
    | ~ r1_tarski(sK15,k2_xboole_0(sK15,sK16))
    | ~ r1_tarski(sK15,sK15) ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_64,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f293])).

cnf(c_4092,plain,
    ( r1_tarski(sK15,sK15) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_76,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f242])).

cnf(c_3913,plain,
    ( r1_tarski(k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)),sK15) ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_62,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f230])).

cnf(c_3721,plain,
    ( ~ r1_tarski(k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)),sK15)
    | ~ r1_tarski(sK15,k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)))
    | k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)) = sK15 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_84,negated_conjecture,
    ( k3_xboole_0(sK15,k2_xboole_0(sK15,sK16)) != sK15 ),
    inference(cnf_transformation,[],[f250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4580,c_4350,c_4092,c_3913,c_3721,c_84])).

%------------------------------------------------------------------------------
