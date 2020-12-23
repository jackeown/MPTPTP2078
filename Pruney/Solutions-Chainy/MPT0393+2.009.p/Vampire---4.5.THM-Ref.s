%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 202 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  331 ( 524 expanded)
%              Number of equality atoms :  181 ( 276 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f142,f1114,f1176,f1368,f1375])).

fof(f1375,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1368,plain,
    ( spl5_20
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1364,f1160,f1153])).

fof(f1153,plain,
    ( spl5_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1160,plain,
    ( spl5_21
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1364,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_21 ),
    inference(resolution,[],[f1161,f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f145,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f145,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f137,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f137,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f122,f47])).

fof(f122,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f56,f64])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1161,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1176,plain,
    ( spl5_21
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f1148,f1112,f1160])).

fof(f1112,plain,
    ( spl5_19
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1148,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_19 ),
    inference(superposition,[],[f105,f1113])).

fof(f1113,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f105,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f74,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1114,plain,
    ( spl5_19
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1110,f112,f1112])).

fof(f112,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1110,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f1087])).

fof(f1087,plain,
    ( sK0 != sK0
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_1 ),
    inference(superposition,[],[f113,f1082])).

fof(f1082,plain,(
    ! [X9] :
      ( k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) ) ),
    inference(global_subsumption,[],[f98,f124,f1081])).

fof(f1081,plain,(
    ! [X9] :
      ( r1_tarski(X9,k1_setfam_1(k2_enumset1(X9,X9,X9,X9)))
      | k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9
      | ~ r1_tarski(X9,X9)
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) ) ),
    inference(forward_demodulation,[],[f1080,f82])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f1080,plain,(
    ! [X9] :
      ( k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9
      | ~ r1_tarski(X9,X9)
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)
      | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9))) ) ),
    inference(forward_demodulation,[],[f1079,f82])).

fof(f1079,plain,(
    ! [X9] :
      ( ~ r1_tarski(X9,X9)
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)
      | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9))
      | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9))) ) ),
    inference(forward_demodulation,[],[f1072,f82])).

fof(f1072,plain,(
    ! [X9] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),X9)
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)
      | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9))
      | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9))) ) ),
    inference(duplicate_literal_removal,[],[f1071])).

fof(f1071,plain,(
    ! [X9] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),X9)
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)
      | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9))
      | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9)))
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) ) ),
    inference(superposition,[],[f192,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
      | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0)))
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(resolution,[],[f52,f102])).

fof(f102,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f192,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_tarski(X2),sK1(X2,k3_tarski(X2)))
      | k1_xboole_0 = X2
      | k3_tarski(X2) = k1_setfam_1(X2) ) ),
    inference(resolution,[],[f53,f123])).

fof(f123,plain,(
    ! [X5] :
      ( ~ r1_tarski(k3_tarski(X5),k1_setfam_1(X5))
      | k3_tarski(X5) = k1_setfam_1(X5) ) ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_setfam_1(k2_enumset1(X6,X6,X6,X6)))
      | k1_setfam_1(k2_enumset1(X6,X6,X6,X6)) = X6 ) ),
    inference(resolution,[],[f56,f119])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(superposition,[],[f49,f82])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f142,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f138,f140])).

fof(f140,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f138,plain,(
    k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f132,f119])).

fof(f114,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f81,f112])).

fof(f81,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f46,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).

fof(f24,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10207)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (10226)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (10207)Refutation not found, incomplete strategy% (10207)------------------------------
% 0.21/0.52  % (10207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10199)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10207)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10207)Memory used [KB]: 10618
% 0.21/0.52  % (10207)Time elapsed: 0.098 s
% 0.21/0.52  % (10207)------------------------------
% 0.21/0.52  % (10207)------------------------------
% 0.21/0.52  % (10208)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (10199)Refutation not found, incomplete strategy% (10199)------------------------------
% 0.21/0.53  % (10199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10199)Memory used [KB]: 10618
% 0.21/0.53  % (10199)Time elapsed: 0.111 s
% 0.21/0.53  % (10199)------------------------------
% 0.21/0.53  % (10199)------------------------------
% 0.21/0.53  % (10204)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10224)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10197)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (10197)Refutation not found, incomplete strategy% (10197)------------------------------
% 0.21/0.54  % (10197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10197)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10197)Memory used [KB]: 1663
% 0.21/0.54  % (10197)Time elapsed: 0.094 s
% 0.21/0.54  % (10197)------------------------------
% 0.21/0.54  % (10197)------------------------------
% 0.21/0.54  % (10202)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (10225)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10198)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (10206)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (10220)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (10201)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.54  % (10217)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (10203)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.55  % (10200)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.55  % (10212)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (10216)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (10220)Refutation not found, incomplete strategy% (10220)------------------------------
% 1.40/0.55  % (10220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (10209)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (10208)Refutation not found, incomplete strategy% (10208)------------------------------
% 1.40/0.55  % (10208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (10208)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (10208)Memory used [KB]: 10746
% 1.40/0.55  % (10208)Time elapsed: 0.136 s
% 1.40/0.55  % (10208)------------------------------
% 1.40/0.55  % (10208)------------------------------
% 1.40/0.55  % (10220)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (10220)Memory used [KB]: 1663
% 1.40/0.55  % (10220)Time elapsed: 0.098 s
% 1.40/0.55  % (10220)------------------------------
% 1.40/0.55  % (10220)------------------------------
% 1.40/0.55  % (10215)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (10210)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.55  % (10222)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.56  % (10211)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.56  % (10218)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.56  % (10218)Refutation not found, incomplete strategy% (10218)------------------------------
% 1.40/0.56  % (10218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (10218)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (10218)Memory used [KB]: 1663
% 1.40/0.56  % (10218)Time elapsed: 0.150 s
% 1.40/0.56  % (10218)------------------------------
% 1.40/0.56  % (10218)------------------------------
% 1.53/0.56  % (10217)Refutation not found, incomplete strategy% (10217)------------------------------
% 1.53/0.56  % (10217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (10217)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (10217)Memory used [KB]: 10746
% 1.53/0.56  % (10217)Time elapsed: 0.148 s
% 1.53/0.56  % (10217)------------------------------
% 1.53/0.56  % (10217)------------------------------
% 1.53/0.56  % (10223)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.57  % (10219)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.58  % (10205)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.58  % (10205)Refutation not found, incomplete strategy% (10205)------------------------------
% 1.53/0.58  % (10205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (10205)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (10205)Memory used [KB]: 10618
% 1.53/0.58  % (10205)Time elapsed: 0.140 s
% 1.53/0.58  % (10205)------------------------------
% 1.53/0.58  % (10205)------------------------------
% 1.53/0.59  % (10221)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.59  % (10214)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.59  % (10214)Refutation not found, incomplete strategy% (10214)------------------------------
% 1.53/0.59  % (10214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (10214)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (10214)Memory used [KB]: 10618
% 1.53/0.59  % (10214)Time elapsed: 0.172 s
% 1.53/0.59  % (10214)------------------------------
% 1.53/0.59  % (10214)------------------------------
% 1.53/0.61  % (10213)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.98/0.64  % (10246)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.98/0.64  % (10250)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.98/0.64  % (10246)Refutation not found, incomplete strategy% (10246)------------------------------
% 1.98/0.64  % (10246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (10246)Termination reason: Refutation not found, incomplete strategy
% 1.98/0.64  
% 1.98/0.64  % (10246)Memory used [KB]: 6140
% 1.98/0.64  % (10246)Time elapsed: 0.062 s
% 1.98/0.64  % (10246)------------------------------
% 1.98/0.64  % (10246)------------------------------
% 1.98/0.65  % (10249)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.98/0.66  % (10216)Refutation found. Thanks to Tanya!
% 1.98/0.66  % SZS status Theorem for theBenchmark
% 1.98/0.66  % SZS output start Proof for theBenchmark
% 1.98/0.66  fof(f1376,plain,(
% 1.98/0.66    $false),
% 1.98/0.66    inference(avatar_sat_refutation,[],[f114,f142,f1114,f1176,f1368,f1375])).
% 1.98/0.66  fof(f1375,plain,(
% 1.98/0.66    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK0 | k1_xboole_0 != k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.98/0.66    introduced(theory_tautology_sat_conflict,[])).
% 1.98/0.66  fof(f1368,plain,(
% 1.98/0.66    spl5_20 | ~spl5_21),
% 1.98/0.66    inference(avatar_split_clause,[],[f1364,f1160,f1153])).
% 1.98/0.66  fof(f1153,plain,(
% 1.98/0.66    spl5_20 <=> k1_xboole_0 = sK0),
% 1.98/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.98/0.66  fof(f1160,plain,(
% 1.98/0.66    spl5_21 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.98/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.98/0.66  fof(f1364,plain,(
% 1.98/0.66    k1_xboole_0 = sK0 | ~spl5_21),
% 1.98/0.66    inference(resolution,[],[f1161,f162])).
% 1.98/0.66  fof(f162,plain,(
% 1.98/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.98/0.66    inference(resolution,[],[f145,f47])).
% 1.98/0.66  fof(f47,plain,(
% 1.98/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f10])).
% 1.98/0.66  fof(f10,axiom,(
% 1.98/0.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.98/0.66  fof(f145,plain,(
% 1.98/0.66    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = X1 | ~r2_hidden(X1,X2)) )),
% 1.98/0.66    inference(resolution,[],[f137,f67])).
% 1.98/0.66  fof(f67,plain,(
% 1.98/0.66    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f22])).
% 1.98/0.66  fof(f22,plain,(
% 1.98/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.98/0.66    inference(flattening,[],[f21])).
% 1.98/0.66  fof(f21,plain,(
% 1.98/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.98/0.66    inference(ennf_transformation,[],[f13])).
% 1.98/0.66  fof(f13,axiom,(
% 1.98/0.66    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.98/0.66  fof(f137,plain,(
% 1.98/0.66    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1) )),
% 1.98/0.66    inference(resolution,[],[f132,f64])).
% 1.98/0.66  fof(f64,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f38])).
% 1.98/0.66  fof(f38,plain,(
% 1.98/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.98/0.66    inference(nnf_transformation,[],[f12])).
% 1.98/0.66  fof(f12,axiom,(
% 1.98/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.98/0.66  fof(f132,plain,(
% 1.98/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.98/0.66    inference(resolution,[],[f122,f47])).
% 1.98/0.66  fof(f122,plain,(
% 1.98/0.66    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_tarski(X3,X4) | X3 = X4) )),
% 1.98/0.66    inference(resolution,[],[f56,f64])).
% 1.98/0.66  fof(f56,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f29])).
% 1.98/0.66  fof(f29,plain,(
% 1.98/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.98/0.66    inference(flattening,[],[f28])).
% 1.98/0.66  fof(f28,plain,(
% 1.98/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.98/0.66    inference(nnf_transformation,[],[f2])).
% 1.98/0.66  fof(f2,axiom,(
% 1.98/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.98/0.66  fof(f1161,plain,(
% 1.98/0.66    r2_hidden(sK0,k1_xboole_0) | ~spl5_21),
% 1.98/0.66    inference(avatar_component_clause,[],[f1160])).
% 1.98/0.66  fof(f1176,plain,(
% 1.98/0.66    spl5_21 | ~spl5_19),
% 1.98/0.66    inference(avatar_split_clause,[],[f1148,f1112,f1160])).
% 1.98/0.66  fof(f1112,plain,(
% 1.98/0.66    spl5_19 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.98/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.98/0.66  fof(f1148,plain,(
% 1.98/0.66    r2_hidden(sK0,k1_xboole_0) | ~spl5_19),
% 1.98/0.66    inference(superposition,[],[f105,f1113])).
% 1.98/0.66  fof(f1113,plain,(
% 1.98/0.66    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_19),
% 1.98/0.66    inference(avatar_component_clause,[],[f1112])).
% 1.98/0.66  fof(f105,plain,(
% 1.98/0.66    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.98/0.66    inference(equality_resolution,[],[f104])).
% 1.98/0.66  fof(f104,plain,(
% 1.98/0.66    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.98/0.66    inference(equality_resolution,[],[f94])).
% 1.98/0.66  fof(f94,plain,(
% 1.98/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.98/0.66    inference(definition_unfolding,[],[f74,f66])).
% 1.98/0.66  fof(f66,plain,(
% 1.98/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f7])).
% 1.98/0.66  fof(f7,axiom,(
% 1.98/0.66    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.66  fof(f74,plain,(
% 1.98/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.98/0.66    inference(cnf_transformation,[],[f45])).
% 1.98/0.66  fof(f45,plain,(
% 1.98/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.98/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 1.98/0.66  fof(f44,plain,(
% 1.98/0.66    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.98/0.66    introduced(choice_axiom,[])).
% 1.98/0.66  fof(f43,plain,(
% 1.98/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.98/0.66    inference(rectify,[],[f42])).
% 1.98/0.66  fof(f42,plain,(
% 1.98/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.98/0.66    inference(flattening,[],[f41])).
% 1.98/0.66  fof(f41,plain,(
% 1.98/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.98/0.66    inference(nnf_transformation,[],[f23])).
% 1.98/0.66  fof(f23,plain,(
% 1.98/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.98/0.66    inference(ennf_transformation,[],[f3])).
% 1.98/0.66  fof(f3,axiom,(
% 1.98/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.98/0.66  fof(f1114,plain,(
% 1.98/0.66    spl5_19 | spl5_1),
% 1.98/0.66    inference(avatar_split_clause,[],[f1110,f112,f1112])).
% 1.98/0.66  fof(f112,plain,(
% 1.98/0.66    spl5_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.98/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.98/0.66  fof(f1110,plain,(
% 1.98/0.66    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl5_1),
% 1.98/0.66    inference(trivial_inequality_removal,[],[f1087])).
% 1.98/0.66  fof(f1087,plain,(
% 1.98/0.66    sK0 != sK0 | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl5_1),
% 1.98/0.66    inference(superposition,[],[f113,f1082])).
% 1.98/0.66  fof(f1082,plain,(
% 1.98/0.66    ( ! [X9] : (k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9 | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)) )),
% 1.98/0.66    inference(global_subsumption,[],[f98,f124,f1081])).
% 1.98/0.66  fof(f1081,plain,(
% 1.98/0.66    ( ! [X9] : (r1_tarski(X9,k1_setfam_1(k2_enumset1(X9,X9,X9,X9))) | k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9 | ~r1_tarski(X9,X9) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)) )),
% 1.98/0.66    inference(forward_demodulation,[],[f1080,f82])).
% 1.98/0.66  fof(f82,plain,(
% 1.98/0.66    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.98/0.66    inference(definition_unfolding,[],[f48,f80])).
% 1.98/0.66  fof(f80,plain,(
% 1.98/0.66    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f50,f79])).
% 1.98/0.66  fof(f79,plain,(
% 1.98/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f51,f66])).
% 1.98/0.66  fof(f51,plain,(
% 1.98/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f6])).
% 1.98/0.66  fof(f6,axiom,(
% 1.98/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.66  fof(f50,plain,(
% 1.98/0.66    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f5])).
% 1.98/0.66  fof(f5,axiom,(
% 1.98/0.66    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.66  fof(f48,plain,(
% 1.98/0.66    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.98/0.66    inference(cnf_transformation,[],[f8])).
% 1.98/0.66  fof(f8,axiom,(
% 1.98/0.66    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.98/0.66  fof(f1080,plain,(
% 1.98/0.66    ( ! [X9] : (k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) = X9 | ~r1_tarski(X9,X9) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9)))) )),
% 1.98/0.66    inference(forward_demodulation,[],[f1079,f82])).
% 1.98/0.66  fof(f1079,plain,(
% 1.98/0.66    ( ! [X9] : (~r1_tarski(X9,X9) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9)))) )),
% 1.98/0.66    inference(forward_demodulation,[],[f1072,f82])).
% 1.98/0.66  fof(f1072,plain,(
% 1.98/0.66    ( ! [X9] : (~r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),X9) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9)))) )),
% 1.98/0.66    inference(duplicate_literal_removal,[],[f1071])).
% 1.98/0.66  fof(f1071,plain,(
% 1.98/0.66    ( ! [X9] : (~r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),X9) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9) | k3_tarski(k2_enumset1(X9,X9,X9,X9)) = k1_setfam_1(k2_enumset1(X9,X9,X9,X9)) | r1_tarski(k3_tarski(k2_enumset1(X9,X9,X9,X9)),k1_setfam_1(k2_enumset1(X9,X9,X9,X9))) | k1_xboole_0 = k2_enumset1(X9,X9,X9,X9)) )),
% 1.98/0.66    inference(superposition,[],[f192,f148])).
% 1.98/0.66  fof(f148,plain,(
% 1.98/0.66    ( ! [X0,X1] : (sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0 | r1_tarski(X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.98/0.66    inference(resolution,[],[f52,f102])).
% 1.98/0.66  fof(f102,plain,(
% 1.98/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.98/0.66    inference(equality_resolution,[],[f86])).
% 1.98/0.66  fof(f86,plain,(
% 1.98/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.98/0.66    inference(definition_unfolding,[],[f60,f80])).
% 1.98/0.66  fof(f60,plain,(
% 1.98/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.98/0.66    inference(cnf_transformation,[],[f37])).
% 1.98/0.66  fof(f37,plain,(
% 1.98/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.98/0.66  fof(f36,plain,(
% 1.98/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.98/0.66    introduced(choice_axiom,[])).
% 1.98/0.66  fof(f35,plain,(
% 1.98/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.66    inference(rectify,[],[f34])).
% 1.98/0.66  fof(f34,plain,(
% 1.98/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.66    inference(nnf_transformation,[],[f4])).
% 1.98/0.66  fof(f4,axiom,(
% 1.98/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.98/0.66  fof(f52,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f27])).
% 1.98/0.66  fof(f27,plain,(
% 1.98/0.66    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 1.98/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).
% 1.98/0.66  fof(f26,plain,(
% 1.98/0.66    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 1.98/0.66    introduced(choice_axiom,[])).
% 1.98/0.66  fof(f19,plain,(
% 1.98/0.66    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.98/0.66    inference(flattening,[],[f18])).
% 1.98/0.66  fof(f18,plain,(
% 1.98/0.66    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.98/0.66    inference(ennf_transformation,[],[f14])).
% 1.98/0.66  fof(f14,axiom,(
% 1.98/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.98/0.66  fof(f192,plain,(
% 1.98/0.66    ( ! [X2] : (~r1_tarski(k3_tarski(X2),sK1(X2,k3_tarski(X2))) | k1_xboole_0 = X2 | k3_tarski(X2) = k1_setfam_1(X2)) )),
% 1.98/0.66    inference(resolution,[],[f53,f123])).
% 1.98/0.66  fof(f123,plain,(
% 1.98/0.66    ( ! [X5] : (~r1_tarski(k3_tarski(X5),k1_setfam_1(X5)) | k3_tarski(X5) = k1_setfam_1(X5)) )),
% 1.98/0.66    inference(resolution,[],[f56,f49])).
% 1.98/0.66  fof(f49,plain,(
% 1.98/0.66    ( ! [X0] : (r1_tarski(k1_setfam_1(X0),k3_tarski(X0))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f11])).
% 1.98/0.66  fof(f11,axiom,(
% 1.98/0.66    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).
% 1.98/0.66  fof(f53,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f27])).
% 1.98/0.66  fof(f124,plain,(
% 1.98/0.66    ( ! [X6] : (~r1_tarski(X6,k1_setfam_1(k2_enumset1(X6,X6,X6,X6))) | k1_setfam_1(k2_enumset1(X6,X6,X6,X6)) = X6) )),
% 1.98/0.66    inference(resolution,[],[f56,f119])).
% 1.98/0.66  fof(f119,plain,(
% 1.98/0.66    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 1.98/0.66    inference(superposition,[],[f49,f82])).
% 1.98/0.66  fof(f98,plain,(
% 1.98/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.98/0.66    inference(equality_resolution,[],[f55])).
% 1.98/0.66  fof(f55,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.98/0.66    inference(cnf_transformation,[],[f29])).
% 1.98/0.66  fof(f113,plain,(
% 1.98/0.66    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 1.98/0.66    inference(avatar_component_clause,[],[f112])).
% 1.98/0.66  fof(f142,plain,(
% 1.98/0.66    spl5_2),
% 1.98/0.66    inference(avatar_split_clause,[],[f138,f140])).
% 1.98/0.66  fof(f140,plain,(
% 1.98/0.66    spl5_2 <=> k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.98/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.98/0.66  fof(f138,plain,(
% 1.98/0.66    k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.98/0.66    inference(resolution,[],[f132,f119])).
% 1.98/0.66  fof(f114,plain,(
% 1.98/0.66    ~spl5_1),
% 1.98/0.66    inference(avatar_split_clause,[],[f81,f112])).
% 1.98/0.66  fof(f81,plain,(
% 1.98/0.66    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.98/0.66    inference(definition_unfolding,[],[f46,f80])).
% 1.98/0.66  fof(f46,plain,(
% 1.98/0.66    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.98/0.66    inference(cnf_transformation,[],[f25])).
% 1.98/0.66  fof(f25,plain,(
% 1.98/0.66    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.98/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 1.98/0.66  fof(f24,plain,(
% 1.98/0.66    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK0 != k1_setfam_1(k1_tarski(sK0))),
% 1.98/0.66    introduced(choice_axiom,[])).
% 1.98/0.66  fof(f17,plain,(
% 1.98/0.66    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.98/0.66    inference(ennf_transformation,[],[f16])).
% 1.98/0.66  fof(f16,negated_conjecture,(
% 1.98/0.66    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.98/0.66    inference(negated_conjecture,[],[f15])).
% 1.98/0.66  fof(f15,conjecture,(
% 1.98/0.66    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.98/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.98/0.66  % SZS output end Proof for theBenchmark
% 1.98/0.66  % (10216)------------------------------
% 1.98/0.66  % (10216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.66  % (10216)Termination reason: Refutation
% 1.98/0.66  
% 1.98/0.66  % (10216)Memory used [KB]: 12025
% 1.98/0.66  % (10216)Time elapsed: 0.234 s
% 1.98/0.66  % (10216)------------------------------
% 1.98/0.66  % (10216)------------------------------
% 2.20/0.68  % (10196)Success in time 0.308 s
%------------------------------------------------------------------------------
