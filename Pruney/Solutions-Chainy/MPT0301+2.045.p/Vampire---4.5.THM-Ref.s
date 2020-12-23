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
% DateTime   : Thu Dec  3 12:41:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 181 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :    6
%              Number of atoms          :  310 ( 482 expanded)
%              Number of equality atoms :   60 ( 108 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f68,f76,f82,f91,f95,f99,f104,f134,f147,f186,f194,f240,f244,f248,f272,f283,f293,f325,f333,f353,f387,f399])).

fof(f399,plain,
    ( spl9_4
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl9_4
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f394,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK0
    | spl9_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f394,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_36
    | ~ spl9_40 ),
    inference(resolution,[],[f321,f247])).

fof(f247,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(k1_xboole_0,X3),X3)
        | k1_xboole_0 = X3 )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl9_36
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | r2_hidden(sK4(k1_xboole_0,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f321,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl9_40
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f387,plain,
    ( spl9_2
    | ~ spl9_36
    | ~ spl9_41 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl9_2
    | ~ spl9_36
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f382,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f382,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_36
    | ~ spl9_41 ),
    inference(resolution,[],[f324,f247])).

fof(f324,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl9_41
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f353,plain,
    ( spl9_1
    | ~ spl9_38
    | ~ spl9_43 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl9_1
    | ~ spl9_38
    | ~ spl9_43 ),
    inference(unit_resulting_resolution,[],[f57,f332,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl9_38
  <=> ! [X0] :
        ( r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f332,plain,
    ( ! [X2,X0,X3,X1] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl9_43
  <=> ! [X1,X3,X0,X2] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f57,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f333,plain,
    ( spl9_43
    | ~ spl9_10
    | ~ spl9_19
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f263,f242,f132,f93,f331])).

fof(f93,plain,
    ( spl9_10
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f132,plain,
    ( spl9_19
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f242,plain,
    ( spl9_35
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
        | r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f263,plain,
    ( ! [X2,X0,X3,X1] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))
    | ~ spl9_10
    | ~ spl9_19
    | ~ spl9_35 ),
    inference(subsumption_resolution,[],[f261,f133])).

fof(f133,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f261,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK8(X1,X2,X0,X3,k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0))) )
    | ~ spl9_10
    | ~ spl9_35 ),
    inference(superposition,[],[f243,f94])).

fof(f94,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f243,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f242])).

fof(f325,plain,
    ( spl9_40
    | spl9_41
    | ~ spl9_7
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f318,f184,f132,f78,f323,f320])).

fof(f78,plain,
    ( spl9_7
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f184,plain,
    ( spl9_27
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X3)
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f315,f133])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_7
    | ~ spl9_27 ),
    inference(superposition,[],[f185,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f185,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f184])).

fof(f293,plain,
    ( spl9_3
    | ~ spl9_38
    | ~ spl9_39 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl9_3
    | ~ spl9_38
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f64,f282,f271])).

fof(f282,plain,
    ( ! [X2,X0,X3,X1] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl9_39
  <=> ! [X1,X3,X0,X2] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f64,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f283,plain,
    ( spl9_39
    | ~ spl9_10
    | ~ spl9_19
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f253,f238,f132,f93,f281])).

fof(f238,plain,
    ( spl9_34
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
        | r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f253,plain,
    ( ! [X2,X0,X3,X1] : ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))
    | ~ spl9_10
    | ~ spl9_19
    | ~ spl9_34 ),
    inference(subsumption_resolution,[],[f251,f133])).

fof(f251,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK7(X1,X0,X2,k1_xboole_0,X3),k1_xboole_0)
        | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3))) )
    | ~ spl9_10
    | ~ spl9_34 ),
    inference(superposition,[],[f239,f94])).

fof(f239,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) )
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f238])).

fof(f272,plain,
    ( spl9_38
    | ~ spl9_11
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f173,f145,f97,f270])).

fof(f97,plain,
    ( spl9_11
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f145,plain,
    ( spl9_21
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f173,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0))
        | k1_xboole_0 = X0 )
    | ~ spl9_11
    | ~ spl9_21 ),
    inference(resolution,[],[f146,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f248,plain,
    ( spl9_36
    | ~ spl9_9
    | ~ spl9_19
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f204,f192,f132,f89,f246])).

fof(f89,plain,
    ( spl9_9
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f192,plain,
    ( spl9_29
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(X0,X1),X0)
        | r2_hidden(sK4(X0,X1),X1)
        | k3_tarski(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f204,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | r2_hidden(sK4(k1_xboole_0,X3),X3) )
    | ~ spl9_9
    | ~ spl9_19
    | ~ spl9_29 ),
    inference(forward_demodulation,[],[f202,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f202,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(k1_xboole_0,X3),X3)
        | k3_tarski(k1_xboole_0) = X3 )
    | ~ spl9_19
    | ~ spl9_29 ),
    inference(resolution,[],[f193,f133])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,X1),X0)
        | r2_hidden(sK4(X0,X1),X1)
        | k3_tarski(X0) = X1 )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f192])).

fof(f244,plain,(
    spl9_35 ),
    inference(avatar_split_clause,[],[f48,f242])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f240,plain,(
    spl9_34 ),
    inference(avatar_split_clause,[],[f47,f238])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
      | r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f194,plain,(
    spl9_29 ),
    inference(avatar_split_clause,[],[f39,f192])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f186,plain,(
    spl9_27 ),
    inference(avatar_split_clause,[],[f45,f184])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f147,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f32,f145])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f134,plain,
    ( spl9_19
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f130,f102,f93,f74,f132])).

fof(f74,plain,
    ( spl9_6
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f102,plain,
    ( spl9_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f130,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f129,f75])).

fof(f75,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(superposition,[],[f103,f94])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f31,f102])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f29,f97])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f95,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f28,f93])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f91,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f25,f89])).

fof(f25,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f82,plain,
    ( spl9_7
    | spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f24,f66,f59,f78])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f76,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f68,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f54,f66,f63])).

fof(f54,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f53,f59,f56])).

fof(f53,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (7765)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (7762)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (7762)Refutation not found, incomplete strategy% (7762)------------------------------
% 0.20/0.47  % (7762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7762)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (7762)Memory used [KB]: 10618
% 0.20/0.47  % (7762)Time elapsed: 0.077 s
% 0.20/0.47  % (7762)------------------------------
% 0.20/0.47  % (7762)------------------------------
% 0.20/0.47  % (7773)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (7770)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (7770)Refutation not found, incomplete strategy% (7770)------------------------------
% 0.20/0.48  % (7770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7770)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7770)Memory used [KB]: 6012
% 0.20/0.48  % (7770)Time elapsed: 0.087 s
% 0.20/0.48  % (7770)------------------------------
% 0.20/0.48  % (7770)------------------------------
% 0.20/0.49  % (7774)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (7761)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (7773)Refutation not found, incomplete strategy% (7773)------------------------------
% 0.20/0.49  % (7773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (7773)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (7773)Memory used [KB]: 1918
% 0.20/0.49  % (7773)Time elapsed: 0.082 s
% 0.20/0.49  % (7773)------------------------------
% 0.20/0.49  % (7773)------------------------------
% 0.20/0.49  % (7767)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (7766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (7780)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (7759)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (7769)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (7780)Refutation not found, incomplete strategy% (7780)------------------------------
% 0.20/0.50  % (7780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7780)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7780)Memory used [KB]: 6140
% 0.20/0.50  % (7780)Time elapsed: 0.107 s
% 0.20/0.50  % (7780)------------------------------
% 0.20/0.50  % (7780)------------------------------
% 0.20/0.50  % (7763)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (7759)Refutation not found, incomplete strategy% (7759)------------------------------
% 0.20/0.50  % (7759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7759)Memory used [KB]: 6140
% 0.20/0.50  % (7759)Time elapsed: 0.091 s
% 0.20/0.50  % (7759)------------------------------
% 0.20/0.50  % (7759)------------------------------
% 0.20/0.50  % (7777)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (7760)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (7763)Refutation not found, incomplete strategy% (7763)------------------------------
% 0.20/0.50  % (7763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7763)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7763)Memory used [KB]: 1663
% 0.20/0.50  % (7763)Time elapsed: 0.093 s
% 0.20/0.50  % (7763)------------------------------
% 0.20/0.50  % (7763)------------------------------
% 0.20/0.50  % (7760)Refutation not found, incomplete strategy% (7760)------------------------------
% 0.20/0.50  % (7760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7760)Memory used [KB]: 10618
% 0.20/0.50  % (7760)Time elapsed: 0.102 s
% 0.20/0.50  % (7760)------------------------------
% 0.20/0.50  % (7760)------------------------------
% 0.20/0.50  % (7775)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (7768)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (7771)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (7769)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f400,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f61,f68,f76,f82,f91,f95,f99,f104,f134,f147,f186,f194,f240,f244,f248,f272,f283,f293,f325,f333,f353,f387,f399])).
% 0.20/0.51  fof(f399,plain,(
% 0.20/0.51    spl9_4 | ~spl9_36 | ~spl9_40),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f398])).
% 0.20/0.51  fof(f398,plain,(
% 0.20/0.51    $false | (spl9_4 | ~spl9_36 | ~spl9_40)),
% 0.20/0.51    inference(subsumption_resolution,[],[f394,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | spl9_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl9_4 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | (~spl9_36 | ~spl9_40)),
% 0.20/0.51    inference(resolution,[],[f321,f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3),X3) | k1_xboole_0 = X3) ) | ~spl9_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f246])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    spl9_36 <=> ! [X3] : (k1_xboole_0 = X3 | r2_hidden(sK4(k1_xboole_0,X3),X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.20/0.51  fof(f321,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f320])).
% 0.20/0.51  fof(f320,plain,(
% 0.20/0.51    spl9_40 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    spl9_2 | ~spl9_36 | ~spl9_41),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f386])).
% 0.20/0.51  fof(f386,plain,(
% 0.20/0.51    $false | (spl9_2 | ~spl9_36 | ~spl9_41)),
% 0.20/0.51    inference(subsumption_resolution,[],[f382,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | spl9_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl9_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.51  fof(f382,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | (~spl9_36 | ~spl9_41)),
% 0.20/0.51    inference(resolution,[],[f324,f247])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_41),
% 0.20/0.51    inference(avatar_component_clause,[],[f323])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    spl9_41 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    spl9_1 | ~spl9_38 | ~spl9_43),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f342])).
% 0.20/0.51  fof(f342,plain,(
% 0.20/0.51    $false | (spl9_1 | ~spl9_38 | ~spl9_43)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f57,f332,f271])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0)) | k1_xboole_0 = X0) ) | ~spl9_38),
% 0.20/0.51    inference(avatar_component_clause,[],[f270])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    spl9_38 <=> ! [X0] : (r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0)) | k1_xboole_0 = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.20/0.51  fof(f332,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))) ) | ~spl9_43),
% 0.20/0.51    inference(avatar_component_clause,[],[f331])).
% 0.20/0.51  fof(f331,plain,(
% 0.20/0.51    spl9_43 <=> ! [X1,X3,X0,X2] : ~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl9_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.51  fof(f333,plain,(
% 0.20/0.51    spl9_43 | ~spl9_10 | ~spl9_19 | ~spl9_35),
% 0.20/0.51    inference(avatar_split_clause,[],[f263,f242,f132,f93,f331])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl9_10 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl9_19 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    spl9_35 <=> ! [X1,X3,X0,X2,X4] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))) ) | (~spl9_10 | ~spl9_19 | ~spl9_35)),
% 0.20/0.51    inference(subsumption_resolution,[],[f261,f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl9_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f132])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X1,X2,X0,X3,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,k1_xboole_0)))) ) | (~spl9_10 | ~spl9_35)),
% 0.20/0.51    inference(superposition,[],[f243,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl9_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) ) | ~spl9_35),
% 0.20/0.51    inference(avatar_component_clause,[],[f242])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    spl9_40 | spl9_41 | ~spl9_7 | ~spl9_19 | ~spl9_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f318,f184,f132,f78,f323,f320])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl9_7 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl9_27 <=> ! [X1,X3,X0,X2] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_7 | ~spl9_19 | ~spl9_27)),
% 0.20/0.51    inference(subsumption_resolution,[],[f315,f133])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_7 | ~spl9_27)),
% 0.20/0.51    inference(superposition,[],[f185,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) ) | ~spl9_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f184])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    spl9_3 | ~spl9_38 | ~spl9_39),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.51  fof(f284,plain,(
% 0.20/0.51    $false | (spl9_3 | ~spl9_38 | ~spl9_39)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f64,f282,f271])).
% 0.20/0.51  fof(f282,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))) ) | ~spl9_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f281])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    spl9_39 <=> ! [X1,X3,X0,X2] : ~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl9_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl9_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.51  fof(f283,plain,(
% 0.20/0.51    spl9_39 | ~spl9_10 | ~spl9_19 | ~spl9_34),
% 0.20/0.51    inference(avatar_split_clause,[],[f253,f238,f132,f93,f281])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    spl9_34 <=> ! [X1,X3,X0,X2,X4] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))) ) | (~spl9_10 | ~spl9_19 | ~spl9_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f251,f133])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X1,X0,X2,k1_xboole_0,X3),k1_xboole_0) | ~r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_xboole_0,X3)))) ) | (~spl9_10 | ~spl9_34)),
% 0.20/0.51    inference(superposition,[],[f239,f94])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) ) | ~spl9_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f238])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    spl9_38 | ~spl9_11 | ~spl9_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f173,f145,f97,f270])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl9_11 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl9_21 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0,X0),k3_xboole_0(X0,X0)) | k1_xboole_0 = X0) ) | (~spl9_11 | ~spl9_21)),
% 0.20/0.51    inference(resolution,[],[f146,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) ) | ~spl9_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f97])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl9_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f145])).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    spl9_36 | ~spl9_9 | ~spl9_19 | ~spl9_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f204,f192,f132,f89,f246])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl9_9 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    spl9_29 <=> ! [X1,X0] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ( ! [X3] : (k1_xboole_0 = X3 | r2_hidden(sK4(k1_xboole_0,X3),X3)) ) | (~spl9_9 | ~spl9_19 | ~spl9_29)),
% 0.20/0.51    inference(forward_demodulation,[],[f202,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl9_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3),X3) | k3_tarski(k1_xboole_0) = X3) ) | (~spl9_19 | ~spl9_29)),
% 0.20/0.51    inference(resolution,[],[f193,f133])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) ) | ~spl9_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f192])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    spl9_35),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f242])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK8(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 0.20/0.51  fof(f240,plain,(
% 0.20/0.51    spl9_34),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f238])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK7(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl9_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f192])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl9_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f184])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    spl9_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f145])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl9_19 | ~spl9_6 | ~spl9_10 | ~spl9_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f130,f102,f93,f74,f132])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl9_6 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl9_12 <=> ! [X1,X0,X2] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl9_6 | ~spl9_10 | ~spl9_12)),
% 0.20/0.51    inference(subsumption_resolution,[],[f129,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl9_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl9_10 | ~spl9_12)),
% 0.20/0.51    inference(superposition,[],[f103,f94])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl9_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f102])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl9_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f102])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl9_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f97])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl9_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f93])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl9_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f89])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl9_7 | spl9_2 | spl9_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f66,f59,f78])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl9_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f74])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ~spl9_3 | ~spl9_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f66,f63])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.51    inference(inner_rewriting,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl9_1 | ~spl9_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f53,f59,f56])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.51    inference(inner_rewriting,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7769)------------------------------
% 0.20/0.51  % (7769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7769)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7769)Memory used [KB]: 10874
% 0.20/0.51  % (7769)Time elapsed: 0.082 s
% 0.20/0.51  % (7769)------------------------------
% 0.20/0.51  % (7769)------------------------------
% 0.20/0.51  % (7756)Success in time 0.155 s
%------------------------------------------------------------------------------
