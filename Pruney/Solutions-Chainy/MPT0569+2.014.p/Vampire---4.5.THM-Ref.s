%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 216 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 ( 775 expanded)
%              Number of equality atoms :   89 ( 165 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f621,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f111,f115,f128,f165,f169,f176,f230,f244,f252,f258,f278,f584,f620])).

fof(f620,plain,(
    ~ spl12_39 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl12_39 ),
    inference(resolution,[],[f565,f116])).

fof(f116,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f61,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f565,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl12_39
  <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f584,plain,
    ( ~ spl12_9
    | spl12_39
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f557,f174,f113,f103,f564,f167])).

fof(f167,plain,
    ( spl12_9
  <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f103,plain,
    ( spl12_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f113,plain,
    ( spl12_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f174,plain,
    ( spl12_10
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f557,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)
    | ~ spl12_1
    | ~ spl12_3
    | ~ spl12_10 ),
    inference(superposition,[],[f432,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f432,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,X0))
        | ~ r2_hidden(sK6(k2_relat_1(sK1),sK0),X0) )
    | ~ spl12_3
    | ~ spl12_10 ),
    inference(resolution,[],[f431,f175])).

fof(f175,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f431,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl12_3 ),
    inference(resolution,[],[f92,f114])).

fof(f114,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f92,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f278,plain,
    ( spl12_7
    | spl12_2 ),
    inference(avatar_split_clause,[],[f266,f106,f154])).

fof(f154,plain,
    ( spl12_7
  <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f106,plain,
    ( spl12_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f266,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))
    | spl12_2 ),
    inference(resolution,[],[f107,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

% (16932)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f107,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f258,plain,(
    ~ spl12_19 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl12_19 ),
    inference(resolution,[],[f251,f116])).

fof(f251,plain,
    ( r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl12_19
  <=> r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f252,plain,
    ( spl12_19
    | ~ spl12_3
    | spl12_18 ),
    inference(avatar_split_clause,[],[f248,f242,f113,f250])).

fof(f242,plain,
    ( spl12_18
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f248,plain,
    ( r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl12_3
    | spl12_18 ),
    inference(trivial_inequality_removal,[],[f247])).

fof(f247,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl12_3
    | spl12_18 ),
    inference(superposition,[],[f243,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(sK1,X0)
        | r2_hidden(sK10(sK5(k10_relat_1(sK1,X0)),X0,sK1),X0) )
    | ~ spl12_3 ),
    inference(resolution,[],[f138,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
        | r2_hidden(sK10(X0,X1,sK1),X1) )
    | ~ spl12_3 ),
    inference(resolution,[],[f75,f114])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK10(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
            & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
        & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f243,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | spl12_18 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( ~ spl12_18
    | spl12_1
    | ~ spl12_16 ),
    inference(avatar_split_clause,[],[f234,f228,f103,f242])).

fof(f228,plain,
    ( spl12_16
  <=> k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f234,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0)
    | spl12_1
    | ~ spl12_16 ),
    inference(superposition,[],[f104,f229])).

fof(f229,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f104,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f230,plain,
    ( spl12_16
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f223,f126,f113,f228])).

fof(f126,plain,
    ( spl12_4
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f223,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(superposition,[],[f211,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f211,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))
    | ~ spl12_3 ),
    inference(resolution,[],[f85,f114])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f65,f62])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f176,plain,
    ( spl12_10
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f171,f163,f174])).

fof(f163,plain,
    ( spl12_8
  <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f171,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl12_8 ),
    inference(resolution,[],[f164,f96])).

fof(f96,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f38,f37,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f164,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f169,plain,
    ( spl12_9
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f159,f154,f167])).

fof(f159,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)
    | ~ spl12_7 ),
    inference(resolution,[],[f155,f100])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f78,f62])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
            | ~ r2_hidden(sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK11(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
          | ~ r2_hidden(sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X1)
            & r2_hidden(sK11(X0,X1,X2),X0) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f155,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f165,plain,
    ( spl12_8
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f158,f154,f163])).

fof(f158,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl12_7 ),
    inference(resolution,[],[f155,f101])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f77,f62])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f128,plain,
    ( spl12_4
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f124,f106,f126])).

fof(f124,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))
    | ~ spl12_2 ),
    inference(resolution,[],[f119,f110])).

fof(f110,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f83,f60])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f51,f113])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f111,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f52,f106,f103])).

fof(f52,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f53,f106,f103])).

fof(f53,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:32:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (16938)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.48  % (16947)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.48  % (16937)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (16939)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (16931)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (16929)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (16927)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (16935)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (16930)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (16928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16925)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (16934)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (16934)Refutation not found, incomplete strategy% (16934)------------------------------
% 0.21/0.50  % (16934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16934)Memory used [KB]: 10618
% 0.21/0.50  % (16934)Time elapsed: 0.116 s
% 0.21/0.50  % (16934)------------------------------
% 0.21/0.50  % (16934)------------------------------
% 0.21/0.50  % (16933)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (16951)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (16943)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (16924)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16949)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (16950)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (16945)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (16941)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (16942)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (16926)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (16952)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (16948)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (16936)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (16953)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.53  % (16935)Refutation not found, incomplete strategy% (16935)------------------------------
% 1.42/0.53  % (16935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.53  % (16935)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.53  
% 1.42/0.53  % (16935)Memory used [KB]: 10618
% 1.42/0.53  % (16935)Time elapsed: 0.142 s
% 1.42/0.53  % (16935)------------------------------
% 1.42/0.53  % (16935)------------------------------
% 1.42/0.53  % (16946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.54  % (16940)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.54  % (16946)Refutation not found, incomplete strategy% (16946)------------------------------
% 1.42/0.54  % (16946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (16946)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (16946)Memory used [KB]: 10746
% 1.42/0.54  % (16946)Time elapsed: 0.146 s
% 1.42/0.54  % (16946)------------------------------
% 1.42/0.54  % (16946)------------------------------
% 1.42/0.54  % (16943)Refutation found. Thanks to Tanya!
% 1.42/0.54  % SZS status Theorem for theBenchmark
% 1.42/0.54  % SZS output start Proof for theBenchmark
% 1.42/0.54  fof(f621,plain,(
% 1.42/0.54    $false),
% 1.42/0.54    inference(avatar_sat_refutation,[],[f108,f111,f115,f128,f165,f169,f176,f230,f244,f252,f258,f278,f584,f620])).
% 1.42/0.54  fof(f620,plain,(
% 1.42/0.54    ~spl12_39),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f618])).
% 1.42/0.54  fof(f618,plain,(
% 1.42/0.54    $false | ~spl12_39),
% 1.42/0.54    inference(resolution,[],[f565,f116])).
% 1.42/0.54  fof(f116,plain,(
% 1.42/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.42/0.54    inference(superposition,[],[f61,f97])).
% 1.42/0.54  fof(f97,plain,(
% 1.42/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f72])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.42/0.54    inference(cnf_transformation,[],[f41])).
% 1.42/0.54  fof(f41,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.54    inference(flattening,[],[f40])).
% 1.42/0.54  fof(f40,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.42/0.54    inference(nnf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.42/0.54  fof(f565,plain,(
% 1.42/0.54    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0) | ~spl12_39),
% 1.42/0.54    inference(avatar_component_clause,[],[f564])).
% 1.42/0.54  fof(f564,plain,(
% 1.42/0.54    spl12_39 <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).
% 1.42/0.54  fof(f584,plain,(
% 1.42/0.54    ~spl12_9 | spl12_39 | ~spl12_1 | ~spl12_3 | ~spl12_10),
% 1.42/0.54    inference(avatar_split_clause,[],[f557,f174,f113,f103,f564,f167])).
% 1.42/0.54  fof(f167,plain,(
% 1.42/0.54    spl12_9 <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.42/0.54  fof(f103,plain,(
% 1.42/0.54    spl12_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.42/0.54  fof(f113,plain,(
% 1.42/0.54    spl12_3 <=> v1_relat_1(sK1)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.42/0.54  fof(f174,plain,(
% 1.42/0.54    spl12_10 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.42/0.54  fof(f557,plain,(
% 1.42/0.54    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k1_xboole_0) | ~r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) | (~spl12_1 | ~spl12_3 | ~spl12_10)),
% 1.42/0.54    inference(superposition,[],[f432,f109])).
% 1.42/0.54  fof(f109,plain,(
% 1.42/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl12_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f103])).
% 1.42/0.54  fof(f432,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,X0)) | ~r2_hidden(sK6(k2_relat_1(sK1),sK0),X0)) ) | (~spl12_3 | ~spl12_10)),
% 1.42/0.54    inference(resolution,[],[f431,f175])).
% 1.42/0.54  fof(f175,plain,(
% 1.42/0.54    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1) | ~spl12_10),
% 1.42/0.54    inference(avatar_component_clause,[],[f174])).
% 1.42/0.54  fof(f431,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK1) | ~r2_hidden(X0,X1) | r2_hidden(X2,k10_relat_1(sK1,X1))) ) | ~spl12_3),
% 1.42/0.54    inference(resolution,[],[f92,f114])).
% 1.42/0.54  fof(f114,plain,(
% 1.42/0.54    v1_relat_1(sK1) | ~spl12_3),
% 1.42/0.54    inference(avatar_component_clause,[],[f113])).
% 1.42/0.54  fof(f92,plain,(
% 1.42/0.54    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 1.42/0.54    inference(equality_resolution,[],[f56])).
% 1.42/0.54  fof(f56,plain,(
% 1.42/0.54    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f27,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(rectify,[],[f24])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.42/0.54  fof(f278,plain,(
% 1.42/0.54    spl12_7 | spl12_2),
% 1.42/0.54    inference(avatar_split_clause,[],[f266,f106,f154])).
% 1.42/0.54  fof(f154,plain,(
% 1.42/0.54    spl12_7 <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.42/0.54  fof(f106,plain,(
% 1.42/0.54    spl12_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.42/0.54  fof(f266,plain,(
% 1.42/0.54    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) | spl12_2),
% 1.42/0.54    inference(resolution,[],[f107,f84])).
% 1.42/0.54  fof(f84,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.42/0.54    inference(definition_unfolding,[],[f63,f62])).
% 1.42/0.54  fof(f62,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f33])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  % (16932)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.54  fof(f17,plain,(
% 1.42/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.42/0.54    inference(ennf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,plain,(
% 1.42/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.54    inference(rectify,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.42/0.54  fof(f107,plain,(
% 1.42/0.54    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl12_2),
% 1.42/0.54    inference(avatar_component_clause,[],[f106])).
% 1.42/0.54  fof(f258,plain,(
% 1.42/0.54    ~spl12_19),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f255])).
% 1.42/0.54  fof(f255,plain,(
% 1.42/0.54    $false | ~spl12_19),
% 1.42/0.54    inference(resolution,[],[f251,f116])).
% 1.42/0.54  fof(f251,plain,(
% 1.42/0.54    r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0) | ~spl12_19),
% 1.42/0.54    inference(avatar_component_clause,[],[f250])).
% 1.42/0.54  fof(f250,plain,(
% 1.42/0.54    spl12_19 <=> r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 1.42/0.54  fof(f252,plain,(
% 1.42/0.54    spl12_19 | ~spl12_3 | spl12_18),
% 1.42/0.54    inference(avatar_split_clause,[],[f248,f242,f113,f250])).
% 1.42/0.54  fof(f242,plain,(
% 1.42/0.54    spl12_18 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 1.42/0.54  fof(f248,plain,(
% 1.42/0.54    r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0) | (~spl12_3 | spl12_18)),
% 1.42/0.54    inference(trivial_inequality_removal,[],[f247])).
% 1.42/0.54  fof(f247,plain,(
% 1.42/0.54    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK10(sK5(k10_relat_1(sK1,k1_xboole_0)),k1_xboole_0,sK1),k1_xboole_0) | (~spl12_3 | spl12_18)),
% 1.42/0.54    inference(superposition,[],[f243,f139])).
% 1.42/0.54  fof(f139,plain,(
% 1.42/0.54    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,X0) | r2_hidden(sK10(sK5(k10_relat_1(sK1,X0)),X0,sK1),X0)) ) | ~spl12_3),
% 1.42/0.54    inference(resolution,[],[f138,f60])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f31])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f16,plain,(
% 1.42/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.42/0.54    inference(ennf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.42/0.54  fof(f138,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(sK10(X0,X1,sK1),X1)) ) | ~spl12_3),
% 1.42/0.54    inference(resolution,[],[f75,f114])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK10(X0,X1,X2),X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).
% 1.42/0.54  fof(f44,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f43,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(rectify,[],[f42])).
% 1.42/0.54  fof(f42,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(nnf_transformation,[],[f19])).
% 1.42/0.54  fof(f19,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(ennf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.42/0.54  fof(f243,plain,(
% 1.42/0.54    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | spl12_18),
% 1.42/0.54    inference(avatar_component_clause,[],[f242])).
% 1.42/0.54  fof(f244,plain,(
% 1.42/0.54    ~spl12_18 | spl12_1 | ~spl12_16),
% 1.42/0.54    inference(avatar_split_clause,[],[f234,f228,f103,f242])).
% 1.42/0.54  fof(f228,plain,(
% 1.42/0.54    spl12_16 <=> k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 1.42/0.54  fof(f234,plain,(
% 1.42/0.54    k1_xboole_0 != k10_relat_1(sK1,k1_xboole_0) | (spl12_1 | ~spl12_16)),
% 1.42/0.54    inference(superposition,[],[f104,f229])).
% 1.42/0.54  fof(f229,plain,(
% 1.42/0.54    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl12_16),
% 1.42/0.54    inference(avatar_component_clause,[],[f228])).
% 1.42/0.54  fof(f104,plain,(
% 1.42/0.54    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl12_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f103])).
% 1.42/0.54  fof(f230,plain,(
% 1.42/0.54    spl12_16 | ~spl12_3 | ~spl12_4),
% 1.42/0.54    inference(avatar_split_clause,[],[f223,f126,f113,f228])).
% 1.42/0.54  fof(f126,plain,(
% 1.42/0.54    spl12_4 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.42/0.54  fof(f223,plain,(
% 1.42/0.54    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | (~spl12_3 | ~spl12_4)),
% 1.42/0.54    inference(superposition,[],[f211,f127])).
% 1.42/0.54  fof(f127,plain,(
% 1.42/0.54    k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) | ~spl12_4),
% 1.42/0.54    inference(avatar_component_clause,[],[f126])).
% 1.42/0.54  fof(f211,plain,(
% 1.42/0.54    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) ) | ~spl12_3),
% 1.42/0.54    inference(resolution,[],[f85,f114])).
% 1.42/0.54  fof(f85,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))) )),
% 1.42/0.54    inference(definition_unfolding,[],[f65,f62])).
% 1.42/0.54  fof(f65,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.42/0.55  fof(f176,plain,(
% 1.42/0.55    spl12_10 | ~spl12_8),
% 1.42/0.55    inference(avatar_split_clause,[],[f171,f163,f174])).
% 1.42/0.55  fof(f163,plain,(
% 1.42/0.55    spl12_8 <=> r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.42/0.55  fof(f171,plain,(
% 1.42/0.55    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),sK0)),sK6(k2_relat_1(sK1),sK0)),sK1) | ~spl12_8),
% 1.42/0.55    inference(resolution,[],[f164,f96])).
% 1.42/0.55  fof(f96,plain,(
% 1.42/0.55    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f66])).
% 1.42/0.55  fof(f66,plain,(
% 1.42/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f35,f38,f37,f36])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.42/0.55    inference(rectify,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.42/0.55  fof(f164,plain,(
% 1.42/0.55    r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~spl12_8),
% 1.42/0.55    inference(avatar_component_clause,[],[f163])).
% 1.42/0.55  fof(f169,plain,(
% 1.42/0.55    spl12_9 | ~spl12_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f159,f154,f167])).
% 1.42/0.55  fof(f159,plain,(
% 1.42/0.55    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) | ~spl12_7),
% 1.42/0.55    inference(resolution,[],[f155,f100])).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X4,X1)) )),
% 1.42/0.55    inference(equality_resolution,[],[f90])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.42/0.55    inference(definition_unfolding,[],[f78,f62])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f50])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK11(X0,X1,X2),X1) | ~r2_hidden(sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f48,f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK11(X0,X1,X2),X1) | ~r2_hidden(sK11(X0,X1,X2),X0) | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(rectify,[],[f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(flattening,[],[f46])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.42/0.55    inference(nnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.42/0.55  fof(f155,plain,(
% 1.42/0.55    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) | ~spl12_7),
% 1.42/0.55    inference(avatar_component_clause,[],[f154])).
% 1.42/0.55  fof(f165,plain,(
% 1.42/0.55    spl12_8 | ~spl12_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f158,f154,f163])).
% 1.42/0.55  fof(f158,plain,(
% 1.42/0.55    r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~spl12_7),
% 1.42/0.55    inference(resolution,[],[f155,f101])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f91])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.42/0.55    inference(definition_unfolding,[],[f77,f62])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.42/0.55    inference(cnf_transformation,[],[f50])).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    spl12_4 | ~spl12_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f124,f106,f126])).
% 1.42/0.55  fof(f124,plain,(
% 1.42/0.55    k1_xboole_0 = k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)) | ~spl12_2),
% 1.42/0.55    inference(resolution,[],[f119,f110])).
% 1.42/0.55  fof(f110,plain,(
% 1.42/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl12_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f106])).
% 1.42/0.55  fof(f119,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.55    inference(resolution,[],[f83,f60])).
% 1.42/0.55  fof(f83,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f64,f62])).
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    spl12_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f51,f113])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    v1_relat_1(sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.42/0.55    inference(flattening,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,plain,(
% 1.42/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.57/0.55  fof(f12,negated_conjecture,(
% 1.57/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.57/0.55    inference(negated_conjecture,[],[f11])).
% 1.57/0.55  fof(f11,conjecture,(
% 1.57/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.57/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.57/0.55  fof(f111,plain,(
% 1.57/0.55    spl12_1 | spl12_2),
% 1.57/0.55    inference(avatar_split_clause,[],[f52,f106,f103])).
% 1.57/0.55  fof(f52,plain,(
% 1.57/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.57/0.55    inference(cnf_transformation,[],[f23])).
% 1.57/0.55  fof(f108,plain,(
% 1.57/0.55    ~spl12_1 | ~spl12_2),
% 1.57/0.55    inference(avatar_split_clause,[],[f53,f106,f103])).
% 1.57/0.55  fof(f53,plain,(
% 1.57/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.57/0.55    inference(cnf_transformation,[],[f23])).
% 1.57/0.55  % SZS output end Proof for theBenchmark
% 1.57/0.55  % (16943)------------------------------
% 1.57/0.55  % (16943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.55  % (16943)Termination reason: Refutation
% 1.57/0.55  
% 1.57/0.55  % (16943)Memory used [KB]: 11129
% 1.57/0.55  % (16943)Time elapsed: 0.156 s
% 1.57/0.55  % (16943)------------------------------
% 1.57/0.55  % (16943)------------------------------
% 1.57/0.55  % (16944)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.55  % (16923)Success in time 0.2 s
%------------------------------------------------------------------------------
