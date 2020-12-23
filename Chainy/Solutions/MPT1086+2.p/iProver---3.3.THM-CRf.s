%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1086+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:00 EST 2020

% Result     : Theorem 39.50s
% Output     : CNFRefutation 39.50s
% Verified   : 
% Statistics : Number of formulae       :   34 (  57 expanded)
%              Number of clauses        :   10 (  12 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 118 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1710,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3630,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1710])).

fof(f3631,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f3630])).

fof(f8366,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f3631])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5293,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5233,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f8373,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f5293,f5233])).

fof(f10025,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f8366,f8373])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5290,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5082,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1713,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1714,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X0) )
       => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1713])).

fof(f3634,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1714])).

fof(f3635,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(flattening,[],[f3634])).

fof(f5076,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k2_xboole_0(X0,X1))
        & v1_finset_1(X1)
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k2_xboole_0(sK601,sK602))
      & v1_finset_1(sK602)
      & v1_finset_1(sK601) ) ),
    introduced(choice_axiom,[])).

fof(f5077,plain,
    ( ~ v1_finset_1(k2_xboole_0(sK601,sK602))
    & v1_finset_1(sK602)
    & v1_finset_1(sK601) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK601,sK602])],[f3635,f5076])).

fof(f8372,plain,(
    ~ v1_finset_1(k2_xboole_0(sK601,sK602)) ),
    inference(cnf_transformation,[],[f5077])).

fof(f10026,plain,(
    ~ v1_finset_1(k5_xboole_0(k5_xboole_0(sK601,sK602),k4_xboole_0(sK601,k4_xboole_0(sK601,sK602)))) ),
    inference(definition_unfolding,[],[f8372,f8373])).

fof(f8371,plain,(
    v1_finset_1(sK602) ),
    inference(cnf_transformation,[],[f5077])).

fof(f8370,plain,(
    v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f5077])).

cnf(c_3262,plain,
    ( ~ v1_finset_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f10025])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5290])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5082])).

cnf(c_46582,plain,
    ( ~ v1_finset_1(X0)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_3262,c_211,c_7])).

cnf(c_124351,plain,
    ( v1_finset_1(k5_xboole_0(sK601,k5_xboole_0(sK602,k4_xboole_0(sK601,k4_xboole_0(sK601,sK602)))))
    | ~ v1_finset_1(sK602)
    | ~ v1_finset_1(sK601) ),
    inference(instantiation,[status(thm)],[c_46582])).

cnf(c_3266,negated_conjecture,
    ( ~ v1_finset_1(k5_xboole_0(k5_xboole_0(sK601,sK602),k4_xboole_0(sK601,k4_xboole_0(sK601,sK602)))) ),
    inference(cnf_transformation,[],[f10026])).

cnf(c_46581,negated_conjecture,
    ( ~ v1_finset_1(k5_xboole_0(sK601,k5_xboole_0(sK602,k4_xboole_0(sK601,k4_xboole_0(sK601,sK602))))) ),
    inference(theory_normalisation,[status(thm)],[c_3266,c_211,c_7])).

cnf(c_3267,negated_conjecture,
    ( v1_finset_1(sK602) ),
    inference(cnf_transformation,[],[f8371])).

cnf(c_3268,negated_conjecture,
    ( v1_finset_1(sK601) ),
    inference(cnf_transformation,[],[f8370])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_124351,c_46581,c_3267,c_3268])).

%------------------------------------------------------------------------------
