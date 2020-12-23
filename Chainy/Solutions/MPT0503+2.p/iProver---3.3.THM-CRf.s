%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0503+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 43.54s
% Output     : CNFRefutation 43.54s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1873,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1896,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1748,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2996,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f1873,f1896,f1748,f1748])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1886,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f3004,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1886,f1748])).

fof(f675,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f676,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(negated_conjecture,[],[f675])).

fof(f1217,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f676])).

fof(f1723,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(k7_relat_1(X1,X0),X0)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK150,sK149) != k7_relat_1(k7_relat_1(sK150,sK149),sK149)
      & v1_relat_1(sK150) ) ),
    introduced(choice_axiom,[])).

fof(f1724,plain,
    ( k7_relat_1(sK150,sK149) != k7_relat_1(k7_relat_1(sK150,sK149),sK149)
    & v1_relat_1(sK150) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149,sK150])],[f1217,f1723])).

fof(f2815,plain,(
    v1_relat_1(sK150) ),
    inference(cnf_transformation,[],[f1724])).

fof(f674,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1216,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f674])).

fof(f2814,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1216])).

fof(f3412,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f2814,f1896])).

fof(f2816,plain,(
    k7_relat_1(sK150,sK149) != k7_relat_1(k7_relat_1(sK150,sK149),sK149) ),
    inference(cnf_transformation,[],[f1724])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2996])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3004])).

cnf(c_31909,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_1061,negated_conjecture,
    ( v1_relat_1(sK150) ),
    inference(cnf_transformation,[],[f2815])).

cnf(c_31084,plain,
    ( v1_relat_1(sK150) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_1059,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3412])).

cnf(c_31085,plain,
    ( k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_64211,plain,
    ( k7_relat_1(sK150,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK150,X0),X1) ),
    inference(superposition,[status(thm)],[c_31084,c_31085])).

cnf(c_64971,plain,
    ( k7_relat_1(k7_relat_1(sK150,X0),X0) = k7_relat_1(sK150,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_31909,c_64211])).

cnf(c_65367,plain,
    ( k7_relat_1(k7_relat_1(sK150,X0),X0) = k7_relat_1(sK150,X0) ),
    inference(light_normalisation,[status(thm)],[c_64971,c_145])).

cnf(c_1060,negated_conjecture,
    ( k7_relat_1(sK150,sK149) != k7_relat_1(k7_relat_1(sK150,sK149),sK149) ),
    inference(cnf_transformation,[],[f2816])).

cnf(c_145926,plain,
    ( k7_relat_1(sK150,sK149) != k7_relat_1(sK150,sK149) ),
    inference(demodulation,[status(thm)],[c_65367,c_1060])).

cnf(c_145928,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_145926])).

%------------------------------------------------------------------------------
