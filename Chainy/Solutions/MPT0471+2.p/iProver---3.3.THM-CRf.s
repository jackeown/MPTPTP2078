%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0471+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:40 EST 2020

% Result     : Theorem 31.85s
% Output     : CNFRefutation 31.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 119 expanded)
%              Number of clauses        :   29 (  32 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 155 expanded)
%              Number of equality atoms :   92 ( 134 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1382,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f1383,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1382])).

fof(f2096,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1383])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1641,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3017,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f2096,f1641,f1641])).

fof(f3326,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f3017])).

fof(f660,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2678,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f660])).

fof(f645,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1149,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f645])).

fof(f2658,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1149])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1849,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1789,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2733,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1849,f1789])).

fof(f3234,plain,(
    ! [X0] :
      ( k5_xboole_0(k5_xboole_0(k1_relat_1(X0),k2_relat_1(X0)),k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2658,f2733])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1846,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1638,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1853,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f2879,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1853,f2733])).

fof(f703,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2729,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f3253,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2729,f1641,f1641])).

fof(f2728,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f3254,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2728,f1641,f1641])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1791,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f2841,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f1791,f1641,f1641])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1803,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f2849,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1803,f1641])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2582,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3212,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2582,f1641])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1089,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2583,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1089])).

fof(f3213,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2583,f1641,f1641])).

fof(f705,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f706,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f705])).

fof(f719,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f706])).

fof(f2732,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f719])).

fof(f3257,plain,(
    o_0_0_xboole_0 != k3_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2732,f1641,f1641])).

cnf(c_448,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3326])).

cnf(c_1030,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2678])).

cnf(c_29069,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_41571,plain,
    ( v1_relat_1(o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_29069])).

cnf(c_1010,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k5_xboole_0(k1_relat_1(X0),k2_relat_1(X0)),k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f3234])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1846])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1638])).

cnf(c_14195,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k2_relat_1(X0))))) = k3_relat_1(X0) ),
    inference(theory_normalisation,[status(thm)],[c_1010,c_211,c_7])).

cnf(c_29089,plain,
    ( k5_xboole_0(k1_relat_1(X0),k5_xboole_0(k2_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k2_relat_1(X0))))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14195])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2879])).

cnf(c_14412,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_31741,plain,
    ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29089,c_14412])).

cnf(c_102783,plain,
    ( k5_xboole_0(k1_relat_1(o_0_0_xboole_0),k4_xboole_0(k2_relat_1(o_0_0_xboole_0),k1_relat_1(o_0_0_xboole_0))) = k3_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_41571,c_31741])).

cnf(c_1080,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3253])).

cnf(c_1081,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3254])).

cnf(c_102785,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)) = k3_relat_1(o_0_0_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_102783,c_1080,c_1081])).

cnf(c_156,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2841])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2849])).

cnf(c_37133,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_102786,plain,
    ( k3_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_102785,c_156,c_37133])).

cnf(c_14480,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_37688,plain,
    ( k3_relat_1(o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k3_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_14480])).

cnf(c_37689,plain,
    ( k3_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k3_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_37688])).

cnf(c_934,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3212])).

cnf(c_1472,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_935,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3213])).

cnf(c_1469,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1084,negated_conjecture,
    ( o_0_0_xboole_0 != k3_relat_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3257])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102786,c_37689,c_1472,c_1469,c_1084])).

%------------------------------------------------------------------------------
