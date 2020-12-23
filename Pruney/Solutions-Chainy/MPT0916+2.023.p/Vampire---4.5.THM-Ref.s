%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 285 expanded)
%              Number of leaves         :   41 ( 128 expanded)
%              Depth                    :    7
%              Number of atoms          :  399 ( 833 expanded)
%              Number of equality atoms :   62 ( 106 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f862,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f80,f122,f131,f152,f161,f166,f226,f355,f409,f437,f450,f455,f467,f518,f534,f535,f536,f601,f691,f741,f752,f756,f758,f770,f810,f856])).

fof(f856,plain,
    ( ~ spl9_35
    | ~ spl9_19
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f854,f735,f163,f343])).

fof(f343,plain,
    ( spl9_35
  <=> r1_xboole_0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f163,plain,
    ( spl9_19
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f735,plain,
    ( spl9_60
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f854,plain,
    ( ~ r1_xboole_0(sK3,k1_xboole_0)
    | ~ spl9_19
    | ~ spl9_60 ),
    inference(resolution,[],[f170,f737])).

fof(f737,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f735])).

fof(f170,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X1)
        | ~ r1_xboole_0(sK3,X1) )
    | ~ spl9_19 ),
    inference(resolution,[],[f165,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f165,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f810,plain,
    ( ~ spl9_54
    | ~ spl9_18
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f807,f767,f158,f683])).

fof(f683,plain,
    ( spl9_54
  <=> r1_xboole_0(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

% (15269)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f158,plain,
    ( spl9_18
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f767,plain,
    ( spl9_62
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f807,plain,
    ( ~ r1_xboole_0(sK4,k1_xboole_0)
    | ~ spl9_18
    | ~ spl9_62 ),
    inference(resolution,[],[f769,f168])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1)
        | ~ r1_xboole_0(sK4,X1) )
    | ~ spl9_18 ),
    inference(resolution,[],[f160,f24])).

fof(f160,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f769,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f767])).

fof(f770,plain,
    ( spl9_62
    | ~ spl9_18
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f760,f383,f158,f767])).

fof(f383,plain,
    ( spl9_40
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f760,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)
    | ~ spl9_18
    | ~ spl9_40 ),
    inference(resolution,[],[f385,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4,X0)
        | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f160,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f385,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f383])).

fof(f758,plain,
    ( spl9_40
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f757,f388,f383])).

fof(f388,plain,
    ( spl9_41
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f757,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl9_41 ),
    inference(resolution,[],[f390,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f390,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f388])).

fof(f756,plain,
    ( spl9_60
    | ~ spl9_19
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f731,f187,f163,f735])).

fof(f187,plain,
    ( spl9_22
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f731,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)
    | ~ spl9_19
    | ~ spl9_22 ),
    inference(resolution,[],[f169,f189])).

fof(f189,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0) )
    | ~ spl9_19 ),
    inference(resolution,[],[f165,f27])).

fof(f752,plain,
    ( spl9_41
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f366,f148,f49,f388])).

fof(f49,plain,
    ( spl9_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f148,plain,
    ( spl9_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f366,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(backward_demodulation,[],[f51,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f148])).

fof(f51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f741,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f691,plain,(
    spl9_54 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | spl9_54 ),
    inference(resolution,[],[f685,f23])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f685,plain,
    ( ~ r1_xboole_0(sK4,k1_xboole_0)
    | spl9_54 ),
    inference(avatar_component_clause,[],[f683])).

fof(f601,plain,
    ( ~ spl9_43
    | ~ spl9_13
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f598,f412,f128,f417])).

fof(f417,plain,
    ( spl9_43
  <=> r1_xboole_0(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f128,plain,
    ( spl9_13
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f412,plain,
    ( spl9_42
  <=> r2_hidden(k2_mcart_1(sK6),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f598,plain,
    ( ~ r1_xboole_0(sK5,k1_xboole_0)
    | ~ spl9_13
    | ~ spl9_42 ),
    inference(resolution,[],[f414,f133])).

fof(f133,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_mcart_1(sK6),X1)
        | ~ r1_xboole_0(sK5,X1) )
    | ~ spl9_13 ),
    inference(resolution,[],[f130,f24])).

fof(f130,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f414,plain,
    ( r2_hidden(k2_mcart_1(sK6),k1_xboole_0)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f412])).

fof(f536,plain,
    ( spl9_14
    | spl9_15
    | spl9_16
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f529,f64,f148,f144,f140,f136])).

fof(f136,plain,
    ( spl9_14
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f140,plain,
    ( spl9_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f144,plain,
    ( spl9_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f64,plain,
    ( spl9_5
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f529,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | ~ spl9_5 ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

% (15274)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f66,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f535,plain,
    ( spl9_20
    | spl9_15
    | spl9_16
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f528,f64,f148,f144,f140,f173])).

fof(f173,plain,
    ( spl9_20
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f528,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f534,plain,
    ( spl9_49
    | spl9_15
    | spl9_16
    | spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f527,f64,f148,f144,f140,f531])).

fof(f531,plain,
    ( spl9_49
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f527,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl9_5 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f518,plain,(
    spl9_43 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl9_43 ),
    inference(resolution,[],[f419,f23])).

fof(f419,plain,
    ( ~ r1_xboole_0(sK5,k1_xboole_0)
    | spl9_43 ),
    inference(avatar_component_clause,[],[f417])).

fof(f467,plain,
    ( spl9_42
    | ~ spl9_13
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f462,f217,f128,f412])).

fof(f217,plain,
    ( spl9_26
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f462,plain,
    ( r2_hidden(k2_mcart_1(sK6),k1_xboole_0)
    | ~ spl9_13
    | ~ spl9_26 ),
    inference(resolution,[],[f219,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5,X0)
        | r2_hidden(k2_mcart_1(sK6),X0) )
    | ~ spl9_13 ),
    inference(resolution,[],[f130,f27])).

fof(f219,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f217])).

fof(f455,plain,
    ( spl9_26
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f454,f222,f217])).

fof(f222,plain,
    ( spl9_27
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f454,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl9_27 ),
    inference(resolution,[],[f224,f31])).

fof(f224,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f222])).

fof(f450,plain,
    ( spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f449,f197,f187])).

fof(f197,plain,
    ( spl9_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f449,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl9_24 ),
    inference(resolution,[],[f199,f31])).

fof(f199,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f437,plain,
    ( spl9_24
    | ~ spl9_1
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f180,f140,f44,f197])).

fof(f44,plain,
    ( spl9_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f180,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f46,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f409,plain,
    ( spl9_27
    | ~ spl9_3
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f401,f144,f54,f222])).

fof(f54,plain,
    ( spl9_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f401,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_3
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f56,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f355,plain,(
    spl9_35 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl9_35 ),
    inference(resolution,[],[f345,f23])).

fof(f345,plain,
    ( ~ r1_xboole_0(sK3,k1_xboole_0)
    | spl9_35 ),
    inference(avatar_component_clause,[],[f343])).

fof(f226,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f166,plain,
    ( spl9_19
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f154,f119,f163])).

fof(f119,plain,
    ( spl9_12
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f154,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl9_12 ),
    inference(resolution,[],[f121,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f121,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f161,plain,
    ( spl9_18
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f153,f119,f158])).

fof(f153,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl9_12 ),
    inference(resolution,[],[f121,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f152,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f131,plain,
    ( spl9_13
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f123,f59,f128])).

fof(f59,plain,
    ( spl9_4
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f123,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl9_4 ),
    inference(resolution,[],[f34,f61])).

fof(f61,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f122,plain,
    ( spl9_12
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f114,f59,f119])).

fof(f114,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl9_4 ),
    inference(resolution,[],[f33,f61])).

fof(f80,plain,
    ( ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f17,f77,f73,f69])).

fof(f69,plain,
    ( spl9_6
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f73,plain,
    ( spl9_7
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f77,plain,
    ( spl9_8
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f17,plain,
    ( ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

% (15263)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f67,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f38,f59])).

fof(f38,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f19,f32])).

fof(f19,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15264)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15268)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15272)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (15279)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (15271)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15270)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15257)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15258)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15256)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15259)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15272)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f862,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f67,f80,f122,f131,f152,f161,f166,f226,f355,f409,f437,f450,f455,f467,f518,f534,f535,f536,f601,f691,f741,f752,f756,f758,f770,f810,f856])).
% 0.21/0.54  fof(f856,plain,(
% 0.21/0.54    ~spl9_35 | ~spl9_19 | ~spl9_60),
% 0.21/0.54    inference(avatar_split_clause,[],[f854,f735,f163,f343])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    spl9_35 <=> r1_xboole_0(sK3,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    spl9_19 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.54  fof(f735,plain,(
% 0.21/0.54    spl9_60 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 0.21/0.54  fof(f854,plain,(
% 0.21/0.54    ~r1_xboole_0(sK3,k1_xboole_0) | (~spl9_19 | ~spl9_60)),
% 0.21/0.54    inference(resolution,[],[f170,f737])).
% 0.21/0.54  fof(f737,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) | ~spl9_60),
% 0.21/0.54    inference(avatar_component_clause,[],[f735])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X1) | ~r1_xboole_0(sK3,X1)) ) | ~spl9_19),
% 0.21/0.54    inference(resolution,[],[f165,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl9_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f163])).
% 0.21/0.54  fof(f810,plain,(
% 0.21/0.54    ~spl9_54 | ~spl9_18 | ~spl9_62),
% 0.21/0.54    inference(avatar_split_clause,[],[f807,f767,f158,f683])).
% 0.21/0.54  fof(f683,plain,(
% 0.21/0.54    spl9_54 <=> r1_xboole_0(sK4,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 0.21/0.54  % (15269)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl9_18 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.54  fof(f767,plain,(
% 0.21/0.54    spl9_62 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 0.21/0.54  fof(f807,plain,(
% 0.21/0.54    ~r1_xboole_0(sK4,k1_xboole_0) | (~spl9_18 | ~spl9_62)),
% 0.21/0.54    inference(resolution,[],[f769,f168])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X1) | ~r1_xboole_0(sK4,X1)) ) | ~spl9_18),
% 0.21/0.54    inference(resolution,[],[f160,f24])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl9_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f158])).
% 0.21/0.54  fof(f769,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) | ~spl9_62),
% 0.21/0.54    inference(avatar_component_clause,[],[f767])).
% 0.21/0.54  fof(f770,plain,(
% 0.21/0.54    spl9_62 | ~spl9_18 | ~spl9_40),
% 0.21/0.54    inference(avatar_split_clause,[],[f760,f383,f158,f767])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    spl9_40 <=> r1_tarski(sK4,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.21/0.54  fof(f760,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) | (~spl9_18 | ~spl9_40)),
% 0.21/0.54    inference(resolution,[],[f385,f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK4,X0) | r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),X0)) ) | ~spl9_18),
% 0.21/0.54    inference(resolution,[],[f160,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    r1_tarski(sK4,k1_xboole_0) | ~spl9_40),
% 0.21/0.54    inference(avatar_component_clause,[],[f383])).
% 0.21/0.54  fof(f758,plain,(
% 0.21/0.54    spl9_40 | ~spl9_41),
% 0.21/0.54    inference(avatar_split_clause,[],[f757,f388,f383])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    spl9_41 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.21/0.54  fof(f757,plain,(
% 0.21/0.54    r1_tarski(sK4,k1_xboole_0) | ~spl9_41),
% 0.21/0.54    inference(resolution,[],[f390,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | ~spl9_41),
% 0.21/0.54    inference(avatar_component_clause,[],[f388])).
% 0.21/0.54  fof(f756,plain,(
% 0.21/0.54    spl9_60 | ~spl9_19 | ~spl9_22),
% 0.21/0.54    inference(avatar_split_clause,[],[f731,f187,f163,f735])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    spl9_22 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.54  fof(f731,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),k1_xboole_0) | (~spl9_19 | ~spl9_22)),
% 0.21/0.54    inference(resolution,[],[f169,f189])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl9_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f187])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK3,X0) | r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),X0)) ) | ~spl9_19),
% 0.21/0.54    inference(resolution,[],[f165,f27])).
% 0.21/0.54  fof(f752,plain,(
% 0.21/0.54    spl9_41 | ~spl9_2 | ~spl9_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f366,f148,f49,f388])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl9_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl9_17 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | (~spl9_2 | ~spl9_17)),
% 0.21/0.54    inference(backward_demodulation,[],[f51,f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl9_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f148])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl9_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f741,plain,(
% 0.21/0.54    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f691,plain,(
% 0.21/0.54    spl9_54),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f690])).
% 0.21/0.54  fof(f690,plain,(
% 0.21/0.54    $false | spl9_54),
% 0.21/0.54    inference(resolution,[],[f685,f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.54  fof(f685,plain,(
% 0.21/0.54    ~r1_xboole_0(sK4,k1_xboole_0) | spl9_54),
% 0.21/0.54    inference(avatar_component_clause,[],[f683])).
% 0.21/0.54  fof(f601,plain,(
% 0.21/0.54    ~spl9_43 | ~spl9_13 | ~spl9_42),
% 0.21/0.54    inference(avatar_split_clause,[],[f598,f412,f128,f417])).
% 0.21/0.54  fof(f417,plain,(
% 0.21/0.54    spl9_43 <=> r1_xboole_0(sK5,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl9_13 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    spl9_42 <=> r2_hidden(k2_mcart_1(sK6),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.21/0.54  fof(f598,plain,(
% 0.21/0.54    ~r1_xboole_0(sK5,k1_xboole_0) | (~spl9_13 | ~spl9_42)),
% 0.21/0.54    inference(resolution,[],[f414,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(k2_mcart_1(sK6),X1) | ~r1_xboole_0(sK5,X1)) ) | ~spl9_13),
% 0.21/0.54    inference(resolution,[],[f130,f24])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl9_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK6),k1_xboole_0) | ~spl9_42),
% 0.21/0.54    inference(avatar_component_clause,[],[f412])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    spl9_14 | spl9_15 | spl9_16 | spl9_17 | ~spl9_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f529,f64,f148,f144,f140,f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl9_14 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl9_15 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl9_16 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl9_5 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.54  fof(f529,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | ~spl9_5),
% 0.21/0.54    inference(resolution,[],[f66,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.54  % (15274)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    spl9_20 | spl9_15 | spl9_16 | spl9_17 | ~spl9_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f528,f64,f148,f144,f140,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl9_20 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.54  fof(f528,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | ~spl9_5),
% 0.21/0.54    inference(resolution,[],[f66,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f32])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f534,plain,(
% 0.21/0.54    spl9_49 | spl9_15 | spl9_16 | spl9_17 | ~spl9_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f527,f64,f148,f144,f140,f531])).
% 0.21/0.54  fof(f531,plain,(
% 0.21/0.54    spl9_49 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 0.21/0.54  fof(f527,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | ~spl9_5),
% 0.21/0.54    inference(resolution,[],[f66,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f32])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f518,plain,(
% 0.21/0.54    spl9_43),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f517])).
% 0.21/0.54  fof(f517,plain,(
% 0.21/0.54    $false | spl9_43),
% 0.21/0.54    inference(resolution,[],[f419,f23])).
% 0.21/0.54  fof(f419,plain,(
% 0.21/0.54    ~r1_xboole_0(sK5,k1_xboole_0) | spl9_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f417])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    spl9_42 | ~spl9_13 | ~spl9_26),
% 0.21/0.54    inference(avatar_split_clause,[],[f462,f217,f128,f412])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    spl9_26 <=> r1_tarski(sK5,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.21/0.54  fof(f462,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK6),k1_xboole_0) | (~spl9_13 | ~spl9_26)),
% 0.21/0.54    inference(resolution,[],[f219,f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK5,X0) | r2_hidden(k2_mcart_1(sK6),X0)) ) | ~spl9_13),
% 0.21/0.54    inference(resolution,[],[f130,f27])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    r1_tarski(sK5,k1_xboole_0) | ~spl9_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f217])).
% 0.21/0.54  fof(f455,plain,(
% 0.21/0.54    spl9_26 | ~spl9_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f454,f222,f217])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    spl9_27 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.21/0.54  fof(f454,plain,(
% 0.21/0.54    r1_tarski(sK5,k1_xboole_0) | ~spl9_27),
% 0.21/0.54    inference(resolution,[],[f224,f31])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl9_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f222])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    spl9_22 | ~spl9_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f449,f197,f187])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl9_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl9_24),
% 0.21/0.54    inference(resolution,[],[f199,f31])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl9_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f197])).
% 0.21/0.54  fof(f437,plain,(
% 0.21/0.54    spl9_24 | ~spl9_1 | ~spl9_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f180,f140,f44,f197])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    spl9_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl9_1 | ~spl9_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f46,f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl9_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f140])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f44])).
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    spl9_27 | ~spl9_3 | ~spl9_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f401,f144,f54,f222])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl9_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.54  fof(f401,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | (~spl9_3 | ~spl9_16)),
% 0.21/0.54    inference(backward_demodulation,[],[f56,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl9_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f144])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f54])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    spl9_35),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    $false | spl9_35),
% 0.21/0.54    inference(resolution,[],[f345,f23])).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    ~r1_xboole_0(sK3,k1_xboole_0) | spl9_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f343])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    spl9_19 | ~spl9_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f154,f119,f163])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl9_12 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl9_12),
% 0.21/0.54    inference(resolution,[],[f121,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl9_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    spl9_18 | ~spl9_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f153,f119,f158])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl9_12),
% 0.21/0.54    inference(resolution,[],[f121,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl9_13 | ~spl9_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f123,f59,f128])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl9_4 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl9_4),
% 0.21/0.54    inference(resolution,[],[f34,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl9_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl9_12 | ~spl9_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f59,f119])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl9_4),
% 0.21/0.54    inference(resolution,[],[f33,f61])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~spl9_6 | ~spl9_7 | ~spl9_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f17,f77,f73,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl9_6 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl9_7 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl9_8 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.21/0.54  % (15263)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl9_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f64])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.54    inference(definition_unfolding,[],[f18,f32])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl9_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f59])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f32])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl9_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f20,f54])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl9_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    spl9_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (15272)------------------------------
% 0.21/0.54  % (15272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15272)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (15272)Memory used [KB]: 11257
% 0.21/0.54  % (15272)Time elapsed: 0.130 s
% 0.21/0.54  % (15272)------------------------------
% 0.21/0.54  % (15272)------------------------------
% 0.21/0.54  % (15260)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (15255)Success in time 0.177 s
%------------------------------------------------------------------------------
