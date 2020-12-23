%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0790+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 27.61s
% Output     : CNFRefutation 27.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 104 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1150,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2307,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1150])).

fof(f5119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2307])).

fof(f1173,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2344,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1173])).

fof(f2345,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2344])).

fof(f5154,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2345])).

fof(f1174,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1175,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) = k1_wellord1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1174])).

fof(f2346,plain,(
    ? [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) != k1_wellord1(X1,X0)
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1175])).

fof(f2347,plain,(
    ? [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) != k1_wellord1(X1,X0)
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2346])).

fof(f3154,plain,
    ( ? [X0,X1] :
        ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) != k1_wellord1(X1,X0)
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k3_relat_1(k2_wellord1(sK296,k1_wellord1(sK296,sK295))) != k1_wellord1(sK296,sK295)
      & v2_wellord1(sK296)
      & v1_relat_1(sK296) ) ),
    introduced(choice_axiom,[])).

fof(f3155,plain,
    ( k3_relat_1(k2_wellord1(sK296,k1_wellord1(sK296,sK295))) != k1_wellord1(sK296,sK295)
    & v2_wellord1(sK296)
    & v1_relat_1(sK296) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK295,sK296])],[f2347,f3154])).

fof(f5157,plain,(
    k3_relat_1(k2_wellord1(sK296,k1_wellord1(sK296,sK295))) != k1_wellord1(sK296,sK295) ),
    inference(cnf_transformation,[],[f3155])).

fof(f5156,plain,(
    v2_wellord1(sK296) ),
    inference(cnf_transformation,[],[f3155])).

fof(f5155,plain,(
    v1_relat_1(sK296) ),
    inference(cnf_transformation,[],[f3155])).

cnf(c_1944,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5119])).

cnf(c_99224,plain,
    ( r1_tarski(k1_wellord1(sK296,sK295),k3_relat_1(sK296))
    | ~ v1_relat_1(sK296) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_1979,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | k3_relat_1(k2_wellord1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f5154])).

cnf(c_92557,plain,
    ( ~ r1_tarski(k1_wellord1(sK296,sK295),k3_relat_1(sK296))
    | ~ v2_wellord1(sK296)
    | ~ v1_relat_1(sK296)
    | k3_relat_1(k2_wellord1(sK296,k1_wellord1(sK296,sK295))) = k1_wellord1(sK296,sK295) ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_1980,negated_conjecture,
    ( k3_relat_1(k2_wellord1(sK296,k1_wellord1(sK296,sK295))) != k1_wellord1(sK296,sK295) ),
    inference(cnf_transformation,[],[f5157])).

cnf(c_1981,negated_conjecture,
    ( v2_wellord1(sK296) ),
    inference(cnf_transformation,[],[f5156])).

cnf(c_1982,negated_conjecture,
    ( v1_relat_1(sK296) ),
    inference(cnf_transformation,[],[f5155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99224,c_92557,c_1980,c_1981,c_1982])).

%------------------------------------------------------------------------------
