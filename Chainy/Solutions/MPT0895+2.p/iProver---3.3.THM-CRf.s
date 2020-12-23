%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0895+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:56 EST 2020

% Result     : Theorem 31.47s
% Output     : CNFRefutation 31.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 372 expanded)
%              Number of clauses        :   42 (  67 expanded)
%              Number of leaves         :   13 ( 108 expanded)
%              Depth                    :   19
%              Number of atoms          :  282 (1119 expanded)
%              Number of equality atoms :  232 ( 977 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1352,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1353,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
      <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(negated_conjecture,[],[f1352])).

fof(f2723,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <~> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(ennf_transformation,[],[f1353])).

fof(f3754,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(nnf_transformation,[],[f2723])).

fof(f3755,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ) ),
    inference(flattening,[],[f3754])).

fof(f3756,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 )
        & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) )
   => ( ( k1_xboole_0 = k4_zfmisc_1(sK393,sK394,sK395,sK396)
        | k1_xboole_0 = sK396
        | k1_xboole_0 = sK395
        | k1_xboole_0 = sK394
        | k1_xboole_0 = sK393 )
      & ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
        | ( k1_xboole_0 != sK396
          & k1_xboole_0 != sK395
          & k1_xboole_0 != sK394
          & k1_xboole_0 != sK393 ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3757,plain,
    ( ( k1_xboole_0 = k4_zfmisc_1(sK393,sK394,sK395,sK396)
      | k1_xboole_0 = sK396
      | k1_xboole_0 = sK395
      | k1_xboole_0 = sK394
      | k1_xboole_0 = sK393 )
    & ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
      | ( k1_xboole_0 != sK396
        & k1_xboole_0 != sK395
        & k1_xboole_0 != sK394
        & k1_xboole_0 != sK393 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK393,sK394,sK395,sK396])],[f3755,f3756])).

fof(f6136,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK393,sK394,sK395,sK396)
    | k1_xboole_0 = sK396
    | k1_xboole_0 = sK395
    | k1_xboole_0 = sK394
    | k1_xboole_0 = sK393 ),
    inference(cnf_transformation,[],[f3757])).

fof(f1277,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5963,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f1277])).

fof(f1275,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5961,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1275])).

fof(f6158,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f5963,f5961])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3771,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6934,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 = sK396
    | o_0_0_xboole_0 = sK395
    | o_0_0_xboole_0 = sK394
    | o_0_0_xboole_0 = sK393 ),
    inference(definition_unfolding,[],[f6136,f3771,f6158,f3771,f3771,f3771,f3771])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2915,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f2916,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2915])).

fof(f4226,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2916])).

fof(f6436,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f4226,f3771,f3771,f3771])).

fof(f1330,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3748,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1330])).

fof(f3749,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f3748])).

fof(f6091,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3749])).

fof(f6896,plain,(
    ! [X2,X0,X1] :
      ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f6091,f3771,f5961,f3771,f3771,f3771])).

fof(f6135,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
    | k1_xboole_0 != sK396 ),
    inference(cnf_transformation,[],[f3757])).

fof(f6935,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK396 ),
    inference(definition_unfolding,[],[f6135,f3771,f6158,f3771])).

fof(f4228,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2916])).

fof(f6434,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f4228,f3771,f3771])).

fof(f7014,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f6434])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4522,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4459,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f6159,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f4459,f3771])).

fof(f6577,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f4522,f6159])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1501,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f297])).

fof(f4157,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1501])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1467,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f3946,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1467])).

fof(f6274,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f3946,f3771])).

fof(f296,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1500,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f296])).

fof(f4156,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1500])).

fof(f6134,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
    | k1_xboole_0 != sK395 ),
    inference(cnf_transformation,[],[f3757])).

fof(f6936,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK395 ),
    inference(definition_unfolding,[],[f6134,f3771,f6158,f3771])).

fof(f6133,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
    | k1_xboole_0 != sK394 ),
    inference(cnf_transformation,[],[f3757])).

fof(f6937,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK394 ),
    inference(definition_unfolding,[],[f6133,f3771,f6158,f3771])).

fof(f6132,plain,
    ( k1_xboole_0 != k4_zfmisc_1(sK393,sK394,sK395,sK396)
    | k1_xboole_0 != sK393 ),
    inference(cnf_transformation,[],[f3757])).

fof(f6938,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK393 ),
    inference(definition_unfolding,[],[f6132,f3771,f6158,f3771])).

fof(f4227,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2916])).

fof(f6435,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f4227,f3771,f3771])).

fof(f7015,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f6435])).

cnf(c_2349,negated_conjecture,
    ( o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 = sK396
    | o_0_0_xboole_0 = sK395
    | o_0_0_xboole_0 = sK394
    | o_0_0_xboole_0 = sK393 ),
    inference(cnf_transformation,[],[f6934])).

cnf(c_452,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f6436])).

cnf(c_93447,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395) = o_0_0_xboole_0
    | sK396 = o_0_0_xboole_0
    | sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2349,c_452])).

cnf(c_2311,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f6896])).

cnf(c_94035,plain,
    ( sK396 = o_0_0_xboole_0
    | sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_93447,c_2311])).

cnf(c_2350,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK396 ),
    inference(cnf_transformation,[],[f6935])).

cnf(c_98472,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),o_0_0_xboole_0) != o_0_0_xboole_0
    | sK396 != o_0_0_xboole_0
    | sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_94035,c_2350])).

cnf(c_98478,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),o_0_0_xboole_0) != o_0_0_xboole_0
    | sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_98472,c_94035])).

cnf(c_450,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7014])).

cnf(c_98479,plain,
    ( sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_98478,c_450])).

cnf(c_98480,plain,
    ( sK395 = o_0_0_xboole_0
    | sK394 = o_0_0_xboole_0
    | sK393 = o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_98479])).

cnf(c_745,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6577])).

cnf(c_381,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4157])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f6274])).

cnf(c_88202,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396))
    | o_0_0_xboole_0 != sK396 ),
    inference(resolution,[status(thm)],[c_181,c_2350])).

cnf(c_89298,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395))
    | o_0_0_xboole_0 != sK396 ),
    inference(resolution,[status(thm)],[c_381,c_88202])).

cnf(c_380,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f4156])).

cnf(c_89451,plain,
    ( ~ v1_xboole_0(sK395)
    | o_0_0_xboole_0 != sK396 ),
    inference(resolution,[status(thm)],[c_89298,c_380])).

cnf(c_86431,plain,
    ( ~ v1_xboole_0(sK395)
    | o_0_0_xboole_0 = sK395 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_2351,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK395 ),
    inference(cnf_transformation,[],[f6936])).

cnf(c_88203,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396))
    | o_0_0_xboole_0 != sK395 ),
    inference(resolution,[status(thm)],[c_181,c_2351])).

cnf(c_89299,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395))
    | o_0_0_xboole_0 != sK395 ),
    inference(resolution,[status(thm)],[c_381,c_88203])).

cnf(c_89461,plain,
    ( ~ v1_xboole_0(sK395)
    | o_0_0_xboole_0 != sK395 ),
    inference(resolution,[status(thm)],[c_89299,c_380])).

cnf(c_89787,plain,
    ( ~ v1_xboole_0(sK395) ),
    inference(global_propositional_subsumption,[status(thm)],[c_89451,c_86431,c_89461])).

cnf(c_2352,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK394 ),
    inference(cnf_transformation,[],[f6937])).

cnf(c_88204,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396))
    | o_0_0_xboole_0 != sK394 ),
    inference(resolution,[status(thm)],[c_181,c_2352])).

cnf(c_89300,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395))
    | o_0_0_xboole_0 != sK394 ),
    inference(resolution,[status(thm)],[c_381,c_88204])).

cnf(c_89469,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK393,sK394))
    | o_0_0_xboole_0 != sK394 ),
    inference(resolution,[status(thm)],[c_89300,c_381])).

cnf(c_90003,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK393,sK394))
    | ~ v1_xboole_0(sK394) ),
    inference(resolution,[status(thm)],[c_89469,c_181])).

cnf(c_90592,plain,
    ( ~ v1_xboole_0(sK394) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_90003,c_380])).

cnf(c_33207,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_103115,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK395)
    | sK395 != X0 ),
    inference(instantiation,[status(thm)],[c_33207])).

cnf(c_103120,plain,
    ( v1_xboole_0(sK395)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK395 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_103115])).

cnf(c_103137,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK394)
    | sK394 != X0 ),
    inference(instantiation,[status(thm)],[c_33207])).

cnf(c_103142,plain,
    ( v1_xboole_0(sK394)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK394 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_103137])).

cnf(c_103166,plain,
    ( sK393 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_98480,c_745,c_86431,c_89461,c_90592,c_103120,c_103142])).

cnf(c_2353,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK393,sK394),sK395),sK396)
    | o_0_0_xboole_0 != sK393 ),
    inference(cnf_transformation,[],[f6938])).

cnf(c_103170,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK394),sK395),sK396) != o_0_0_xboole_0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_103166,c_2353])).

cnf(c_103189,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK394),sK395),sK396) != o_0_0_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_103170])).

cnf(c_451,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7015])).

cnf(c_103191,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_103189,c_451])).

cnf(c_103192,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_103191])).

%------------------------------------------------------------------------------
