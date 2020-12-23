%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 217 expanded)
%              Number of leaves         :   34 (  94 expanded)
%              Depth                    :    8
%              Number of atoms          :  309 ( 539 expanded)
%              Number of equality atoms :   79 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f69,f91,f93,f117,f130,f142,f148,f158,f174,f196,f218,f230,f236,f557,f577,f712,f1236])).

fof(f1236,plain,
    ( ~ spl4_16
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f1224])).

fof(f1224,plain,
    ( $false
    | ~ spl4_16
    | spl4_56 ),
    inference(unit_resulting_resolution,[],[f601,f1029])).

fof(f1029,plain,
    ( ! [X1] : k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f1024,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1024,plain,
    ( ! [X1] : k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1))
    | ~ spl4_16 ),
    inference(superposition,[],[f243,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

% (12270)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f243,plain,
    ( ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f239,f35])).

fof(f239,plain,
    ( ! [X1] : k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))
    | ~ spl4_16 ),
    inference(superposition,[],[f47,f207])).

fof(f207,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl4_16
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f601,plain,
    ( k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl4_56
  <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f712,plain,
    ( ~ spl4_56
    | ~ spl4_10
    | ~ spl4_49
    | spl4_51 ),
    inference(avatar_split_clause,[],[f711,f574,f554,f145,f599])).

fof(f145,plain,
    ( spl4_10
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f554,plain,
    ( spl4_49
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f574,plain,
    ( spl4_51
  <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f711,plain,
    ( k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl4_10
    | ~ spl4_49
    | spl4_51 ),
    inference(superposition,[],[f576,f565])).

fof(f565,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK0,sK2))
    | ~ spl4_10
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f250,f556])).

fof(f556,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f554])).

fof(f250,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2)) = k3_xboole_0(X0,k3_subset_1(sK0,sK2))
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f147,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f147,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f576,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f574])).

fof(f577,plain,
    ( ~ spl4_51
    | spl4_19
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f564,f554,f233,f574])).

fof(f233,plain,
    ( spl4_19
  <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f564,plain,
    ( k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl4_19
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f235,f556])).

fof(f235,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f557,plain,
    ( spl4_49
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f549,f227,f87,f554])).

fof(f87,plain,
    ( spl4_5
  <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f227,plain,
    ( spl4_18
  <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f549,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f89,f229])).

fof(f229,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f227])).

fof(f89,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f236,plain,
    ( ~ spl4_19
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f231,f66,f56,f233])).

fof(f56,plain,
    ( spl4_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f66,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f231,plain,
    ( k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f58,f95])).

fof(f95,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f68,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f58,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f230,plain,
    ( spl4_18
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f223,f183,f227])).

fof(f183,plain,
    ( spl4_14
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f223,plain,
    ( k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f50,f185])).

fof(f185,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f218,plain,
    ( spl4_16
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f203,f170,f205])).

fof(f170,plain,
    ( spl4_13
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f203,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_13 ),
    inference(superposition,[],[f35,f172])).

fof(f172,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f196,plain,
    ( spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f181,f154,f183])).

fof(f154,plain,
    ( spl4_11
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f181,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f35,f156])).

fof(f156,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f174,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f168,f138,f170])).

fof(f138,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f168,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f140,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (12269)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f140,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f158,plain,
    ( spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f152,f126,f154])).

fof(f126,plain,
    ( spl4_8
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f152,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f128,f41])).

fof(f128,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f148,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f143,f87,f145])).

fof(f143,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f89])).

fof(f33,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

% (12258)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f142,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f133,f106,f138])).

fof(f106,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f133,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f108,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f108,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f130,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f121,f82,f126])).

fof(f82,plain,
    ( spl4_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f121,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f84,f54])).

fof(f84,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f117,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f116,f66,f106])).

fof(f116,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f101,f32])).

fof(f32,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f101,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f93,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f92,f61,f82])).

fof(f61,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

% (12258)Refutation not found, incomplete strategy% (12258)------------------------------
% (12258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12258)Termination reason: Refutation not found, incomplete strategy

% (12258)Memory used [KB]: 1663
% (12258)Time elapsed: 0.126 s
% (12258)------------------------------
% (12258)------------------------------
fof(f91,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f76,f61,f87])).

fof(f76,plain,
    ( k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f69,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f64,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (12259)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (12283)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (12261)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (12262)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12267)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12267)Refutation not found, incomplete strategy% (12267)------------------------------
% 0.21/0.52  % (12267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12267)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12267)Memory used [KB]: 10618
% 0.21/0.52  % (12267)Time elapsed: 0.097 s
% 0.21/0.52  % (12267)------------------------------
% 0.21/0.52  % (12267)------------------------------
% 0.21/0.53  % (12277)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (12263)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (12283)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1237,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f59,f64,f69,f91,f93,f117,f130,f142,f148,f158,f174,f196,f218,f230,f236,f557,f577,f712,f1236])).
% 0.21/0.53  fof(f1236,plain,(
% 0.21/0.53    ~spl4_16 | spl4_56),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1224])).
% 0.21/0.53  fof(f1224,plain,(
% 0.21/0.53    $false | (~spl4_16 | spl4_56)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f601,f1029])).
% 0.21/0.53  fof(f1029,plain,(
% 0.21/0.53    ( ! [X1] : (k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) ) | ~spl4_16),
% 0.21/0.53    inference(forward_demodulation,[],[f1024,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f1024,plain,(
% 0.21/0.53    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ) | ~spl4_16),
% 0.21/0.53    inference(superposition,[],[f243,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  % (12270)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) ) | ~spl4_16),
% 0.21/0.53    inference(forward_demodulation,[],[f239,f35])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ( ! [X1] : (k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))) ) | ~spl4_16),
% 0.21/0.53    inference(superposition,[],[f47,f207])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    spl4_16 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.21/0.53  fof(f601,plain,(
% 0.21/0.53    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | spl4_56),
% 0.21/0.53    inference(avatar_component_clause,[],[f599])).
% 0.21/0.53  fof(f599,plain,(
% 0.21/0.53    spl4_56 <=> k6_subset_1(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.53  fof(f712,plain,(
% 0.21/0.53    ~spl4_56 | ~spl4_10 | ~spl4_49 | spl4_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f711,f574,f554,f145,f599])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    spl4_10 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.53  fof(f554,plain,(
% 0.21/0.53    spl4_49 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    spl4_51 <=> k6_subset_1(sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.53  fof(f711,plain,(
% 0.21/0.53    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl4_10 | ~spl4_49 | spl4_51)),
% 0.21/0.53    inference(superposition,[],[f576,f565])).
% 0.21/0.53  fof(f565,plain,(
% 0.21/0.53    ( ! [X0] : (k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k5_xboole_0(sK0,sK2))) ) | (~spl4_10 | ~spl4_49)),
% 0.21/0.53    inference(backward_demodulation,[],[f250,f556])).
% 0.21/0.53  fof(f556,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_49),
% 0.21/0.53    inference(avatar_component_clause,[],[f554])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ( ! [X0] : (k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2)) = k3_xboole_0(X0,k3_subset_1(sK0,sK2))) ) | ~spl4_10),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f147,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  fof(f576,plain,(
% 0.21/0.53    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | spl4_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f574])).
% 0.21/0.53  fof(f577,plain,(
% 0.21/0.53    ~spl4_51 | spl4_19 | ~spl4_49),
% 0.21/0.53    inference(avatar_split_clause,[],[f564,f554,f233,f574])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    spl4_19 <=> k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k6_subset_1(sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.53  fof(f564,plain,(
% 0.21/0.53    k6_subset_1(sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | (spl4_19 | ~spl4_49)),
% 0.21/0.53    inference(backward_demodulation,[],[f235,f556])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | spl4_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f233])).
% 0.21/0.53  fof(f557,plain,(
% 0.21/0.53    spl4_49 | ~spl4_5 | ~spl4_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f549,f227,f87,f554])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl4_5 <=> k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    spl4_18 <=> k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f549,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl4_5 | ~spl4_18)),
% 0.21/0.53    inference(backward_demodulation,[],[f89,f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f227])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f87])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ~spl4_19 | spl4_1 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f231,f66,f56,f233])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    spl4_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) | (spl4_1 | ~spl4_3)),
% 0.21/0.53    inference(backward_demodulation,[],[f58,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)) ) | ~spl4_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f68,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f34])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f66])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f56])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    spl4_18 | ~spl4_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f223,f183,f227])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl4_14 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl4_14),
% 0.21/0.53    inference(superposition,[],[f50,f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f183])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    spl4_16 | ~spl4_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f203,f170,f205])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    spl4_13 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_13),
% 0.21/0.53    inference(superposition,[],[f35,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f170])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    spl4_14 | ~spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f181,f154,f183])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    spl4_11 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK0,sK2) | ~spl4_11),
% 0.21/0.53    inference(superposition,[],[f35,f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f154])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    spl4_13 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f168,f138,f170])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl4_9 <=> r1_tarski(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f140,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  % (12269)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    r1_tarski(sK1,sK0) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    spl4_11 | ~spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f152,f126,f154])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl4_8 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    sK2 = k3_xboole_0(sK2,sK0) | ~spl4_8),
% 0.21/0.53    inference(resolution,[],[f128,f41])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | ~spl4_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl4_10 | ~spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f143,f87,f145])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_5),
% 0.21/0.53    inference(superposition,[],[f33,f89])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.53  % (12258)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl4_9 | ~spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f133,f106,f138])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl4_6 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    r1_tarski(sK1,sK0) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f108,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(rectify,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl4_8 | ~spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f121,f82,f126])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl4_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0) | ~spl4_4),
% 0.21/0.53    inference(resolution,[],[f84,f54])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl4_6 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f116,f66,f106])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f68,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl4_4 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f92,f61,f82])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f32])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.53    inference(resolution,[],[f63,f37])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  % (12258)Refutation not found, incomplete strategy% (12258)------------------------------
% 0.21/0.53  % (12258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12258)Memory used [KB]: 1663
% 0.21/0.53  % (12258)Time elapsed: 0.126 s
% 0.21/0.53  % (12258)------------------------------
% 0.21/0.53  % (12258)------------------------------
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl4_5 | ~spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f76,f61,f87])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) | ~spl4_2),
% 0.21/0.53    inference(resolution,[],[f63,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f34])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f56])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (12283)------------------------------
% 0.21/0.54  % (12283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12283)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (12283)Memory used [KB]: 7036
% 0.21/0.54  % (12283)Time elapsed: 0.089 s
% 0.21/0.54  % (12283)------------------------------
% 0.21/0.54  % (12283)------------------------------
% 0.21/0.54  % (12257)Success in time 0.175 s
%------------------------------------------------------------------------------
