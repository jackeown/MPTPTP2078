%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0505+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:42 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :   40 (  83 expanded)
%              Number of clauses        :   18 (  25 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 183 expanded)
%              Number of equality atoms :   40 (  84 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1750,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1902,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2932,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f1750,f1902,f1902])).

fof(f677,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f678,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f677])).

fof(f1222,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f678])).

fof(f1223,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1222])).

fof(f1729,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK151,sK149) != k7_relat_1(k7_relat_1(sK151,sK150),sK149)
      & r1_tarski(sK149,sK150)
      & v1_relat_1(sK151) ) ),
    introduced(choice_axiom,[])).

fof(f1730,plain,
    ( k7_relat_1(sK151,sK149) != k7_relat_1(k7_relat_1(sK151,sK150),sK149)
    & r1_tarski(sK149,sK150)
    & v1_relat_1(sK151) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149,sK150,sK151])],[f1223,f1729])).

fof(f2823,plain,(
    v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f1730])).

fof(f674,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1218,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f674])).

fof(f2820,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1218])).

fof(f3421,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f2820,f1902])).

fof(f2825,plain,(
    k7_relat_1(sK151,sK149) != k7_relat_1(k7_relat_1(sK151,sK150),sK149) ),
    inference(cnf_transformation,[],[f1730])).

fof(f2824,plain,(
    r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f1730])).

fof(f676,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1220,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f676])).

fof(f1221,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1220])).

fof(f2822,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1221])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2932])).

cnf(c_1064,negated_conjecture,
    ( v1_relat_1(sK151) ),
    inference(cnf_transformation,[],[f2823])).

cnf(c_47924,plain,
    ( v1_relat_1(sK151) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_1059,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3421])).

cnf(c_47928,plain,
    ( k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_96517,plain,
    ( k7_relat_1(sK151,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK151,X0),X1) ),
    inference(superposition,[status(thm)],[c_47924,c_47928])).

cnf(c_97385,plain,
    ( k7_relat_1(sK151,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k7_relat_1(sK151,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_96517])).

cnf(c_99140,plain,
    ( k7_relat_1(k7_relat_1(sK151,X0),X1) = k7_relat_1(k7_relat_1(sK151,X1),X0) ),
    inference(superposition,[status(thm)],[c_97385,c_96517])).

cnf(c_1062,negated_conjecture,
    ( k7_relat_1(sK151,sK149) != k7_relat_1(k7_relat_1(sK151,sK150),sK149) ),
    inference(cnf_transformation,[],[f2825])).

cnf(c_99468,plain,
    ( k7_relat_1(k7_relat_1(sK151,sK149),sK150) != k7_relat_1(sK151,sK149) ),
    inference(demodulation,[status(thm)],[c_99140,c_1062])).

cnf(c_1063,negated_conjecture,
    ( r1_tarski(sK149,sK150) ),
    inference(cnf_transformation,[],[f2824])).

cnf(c_47925,plain,
    ( r1_tarski(sK149,sK150) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1061,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f2822])).

cnf(c_47926,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_89753,plain,
    ( k7_relat_1(k7_relat_1(X0,sK149),sK150) = k7_relat_1(X0,sK149)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_47925,c_47926])).

cnf(c_90570,plain,
    ( k7_relat_1(k7_relat_1(sK151,sK149),sK150) = k7_relat_1(sK151,sK149) ),
    inference(superposition,[status(thm)],[c_47924,c_89753])).

cnf(c_99469,plain,
    ( k7_relat_1(sK151,sK149) != k7_relat_1(sK151,sK149) ),
    inference(light_normalisation,[status(thm)],[c_99468,c_90570])).

cnf(c_99470,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_99469])).

%------------------------------------------------------------------------------
