%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 252 expanded)
%              Number of leaves         :   32 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  426 (1013 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f90,f111,f119,f127,f132,f190,f253,f259,f262,f277,f314,f325,f412,f418])).

fof(f418,plain,
    ( ~ spl10_18
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f338,f311,f107,f68,f193])).

fof(f193,plain,
    ( spl10_18
  <=> m1_subset_1(sK8(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f68,plain,
    ( spl10_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK4,X4),sK3)
        | ~ m1_subset_1(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f107,plain,
    ( spl10_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f311,plain,
    ( spl10_29
  <=> r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f338,plain,
    ( ~ m1_subset_1(sK8(sK3,sK4),sK2)
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f313,f163])).

fof(f163,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k11_relat_1(sK3,sK4))
        | ~ m1_subset_1(X3,sK2) )
    | ~ spl10_2
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f155,f109])).

fof(f109,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f155,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k11_relat_1(sK3,sK4))
        | ~ v1_relat_1(sK3)
        | ~ m1_subset_1(X3,sK2) )
    | ~ spl10_2 ),
    inference(resolution,[],[f54,f69])).

fof(f69,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK4,X4),sK3)
        | ~ m1_subset_1(X4,sK2) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f313,plain,
    ( r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f311])).

% (14920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f412,plain,
    ( ~ spl10_6
    | ~ spl10_9
    | spl10_30 ),
    inference(avatar_contradiction_clause,[],[f405])).

% (14912)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f405,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_9
    | spl10_30 ),
    inference(unit_resulting_resolution,[],[f324,f403])).

fof(f403,plain,
    ( ! [X0] : m1_subset_1(k11_relat_1(sK3,X0),k1_zfmisc_1(sK2))
    | ~ spl10_6
    | ~ spl10_9 ),
    inference(superposition,[],[f394,f137])).

fof(f137,plain,
    ( ! [X0] : k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f109,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f394,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK2))
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f334,f388])).

fof(f388,plain,
    ( ! [X0] : k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f89,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f334,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(sK1,sK2,sK3,X0),k1_zfmisc_1(sK2))
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f89,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f324,plain,
    ( ~ m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2))
    | spl10_30 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl10_30
  <=> m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f325,plain,
    ( ~ spl10_30
    | spl10_18
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f319,f311,f193,f322])).

fof(f319,plain,
    ( ~ m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2))
    | spl10_18
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f195,f313,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f195,plain,
    ( ~ m1_subset_1(sK8(sK3,sK4),sK2)
    | spl10_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f314,plain,
    ( spl10_29
    | ~ spl10_9
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f298,f187,f107,f311])).

fof(f187,plain,
    ( spl10_17
  <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f298,plain,
    ( r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4))
    | ~ spl10_9
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f109,f189,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f189,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f277,plain,
    ( spl10_11
    | ~ spl10_1
    | ~ spl10_25 ),
    inference(avatar_split_clause,[],[f266,f250,f64,f124])).

fof(f124,plain,
    ( spl10_11
  <=> r2_hidden(sK4,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f64,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f250,plain,
    ( spl10_25
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f266,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl10_1
    | ~ spl10_25 ),
    inference(backward_demodulation,[],[f65,f252])).

fof(f252,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f65,plain,
    ( r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f262,plain,
    ( ~ spl10_11
    | spl10_10 ),
    inference(avatar_split_clause,[],[f220,f115,f124])).

fof(f115,plain,
    ( spl10_10
  <=> sP9(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f220,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f60,f205,f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK3)
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | sP9(X5,X0) ) ),
    inference(cnf_transformation,[],[f61_D])).

fof(f61_D,plain,(
    ! [X0,X5] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0)
    <=> ~ sP9(X5,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f116,plain,
    ( ~ sP9(sK4,sK3)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f60,plain,(
    ! [X0] : sP0(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f3,f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f259,plain,
    ( ~ spl10_6
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl10_6
    | spl10_12 ),
    inference(subsumption_resolution,[],[f257,f89])).

fof(f257,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl10_12 ),
    inference(subsumption_resolution,[],[f248,f60])).

fof(f248,plain,
    ( ~ sP0(sK3,k1_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl10_12 ),
    inference(superposition,[],[f131,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f131,plain,
    ( ~ sP0(sK3,k1_relset_1(sK1,sK2,sK3))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl10_12
  <=> sP0(sK3,k1_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f253,plain,
    ( spl10_25
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f246,f87,f250])).

fof(f246,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f89,f56])).

fof(f190,plain,
    ( spl10_17
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f181,f124,f187])).

fof(f181,plain,
    ( r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3)
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f60,f126,f47])).

fof(f126,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f132,plain,
    ( ~ spl10_12
    | spl10_1
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f120,f115,f64,f129])).

fof(f120,plain,
    ( ~ sP0(sK3,k1_relset_1(sK1,sK2,sK3))
    | spl10_1
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f66,f117,f62])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( ~ sP9(X5,X0)
      | ~ sP0(X0,X1)
      | r2_hidden(X5,X1) ) ),
    inference(general_splitting,[],[f48,f61_D])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f117,plain,
    ( sP9(sK4,sK3)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f66,plain,
    ( ~ r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f127,plain,
    ( spl10_11
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f121,f115,f124])).

fof(f121,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f60,f117,f62])).

fof(f119,plain,
    ( spl10_10
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f113,f72,f115])).

fof(f72,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f113,plain,
    ( sP9(sK4,sK3)
    | ~ spl10_3 ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f111,plain,
    ( spl10_9
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f105,f87,f107])).

fof(f105,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f55,f89])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f90,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(sK4,X4),sK3)
          | ~ m1_subset_1(X4,sK2) )
      | ~ r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK5),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) )
    & m1_subset_1(sK4,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f24,f29,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X3,X5),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(sK1,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(sK1,X1,X2)) )
                  & m1_subset_1(X3,sK1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k1_relset_1(sK1,X1,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X3,X5),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k1_relset_1(sK1,X1,X2)) )
                & m1_subset_1(X3,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ m1_subset_1(X4,sK2) )
                | ~ r2_hidden(X3,k1_relset_1(sK1,sK2,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X3,X5),X2)
                    & m1_subset_1(X5,sK2) )
                | r2_hidden(X3,k1_relset_1(sK1,sK2,X2)) )
              & m1_subset_1(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                  | ~ m1_subset_1(X4,sK2) )
              | ~ r2_hidden(X3,k1_relset_1(sK1,sK2,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X3,X5),X2)
                  & m1_subset_1(X5,sK2) )
              | r2_hidden(X3,k1_relset_1(sK1,sK2,X2)) )
            & m1_subset_1(X3,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
                | ~ m1_subset_1(X4,sK2) )
            | ~ r2_hidden(X3,k1_relset_1(sK1,sK2,sK3)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X3,X5),sK3)
                & m1_subset_1(X5,sK2) )
            | r2_hidden(X3,k1_relset_1(sK1,sK2,sK3)) )
          & m1_subset_1(X3,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X3,X4),sK3)
              | ~ m1_subset_1(X4,sK2) )
          | ~ r2_hidden(X3,k1_relset_1(sK1,sK2,sK3)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X3,X5),sK3)
              & m1_subset_1(X5,sK2) )
          | r2_hidden(X3,k1_relset_1(sK1,sK2,sK3)) )
        & m1_subset_1(X3,sK1) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(sK4,X4),sK3)
            | ~ m1_subset_1(X4,sK2) )
        | ~ r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(sK4,X5),sK3)
            & m1_subset_1(X5,sK2) )
        | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) )
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(sK4,X5),sK3)
        & m1_subset_1(X5,sK2) )
   => ( r2_hidden(k4_tarski(sK4,sK5),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X3,X5),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X3,X4),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (14910)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

fof(f75,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f44,f72,f64])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f45,f68,f64])).

fof(f45,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK4,X4),sK3)
      | ~ m1_subset_1(X4,sK2)
      | ~ r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (14916)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (14924)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (14911)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (14909)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14924)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (14909)Refutation not found, incomplete strategy% (14909)------------------------------
% 0.22/0.51  % (14909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (14915)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (14913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (14908)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (14914)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (14909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14909)Memory used [KB]: 10618
% 0.22/0.51  % (14909)Time elapsed: 0.087 s
% 0.22/0.51  % (14909)------------------------------
% 0.22/0.51  % (14909)------------------------------
% 0.22/0.52  % (14925)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (14918)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (14928)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f424,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f70,f75,f90,f111,f119,f127,f132,f190,f253,f259,f262,f277,f314,f325,f412,f418])).
% 0.22/0.52  fof(f418,plain,(
% 0.22/0.52    ~spl10_18 | ~spl10_2 | ~spl10_9 | ~spl10_29),
% 0.22/0.52    inference(avatar_split_clause,[],[f338,f311,f107,f68,f193])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    spl10_18 <=> m1_subset_1(sK8(sK3,sK4),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl10_2 <=> ! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3) | ~m1_subset_1(X4,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl10_9 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.52  fof(f311,plain,(
% 0.22/0.52    spl10_29 <=> r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    ~m1_subset_1(sK8(sK3,sK4),sK2) | (~spl10_2 | ~spl10_9 | ~spl10_29)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f313,f163])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,k11_relat_1(sK3,sK4)) | ~m1_subset_1(X3,sK2)) ) | (~spl10_2 | ~spl10_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl10_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,k11_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | ~m1_subset_1(X3,sK2)) ) | ~spl10_2),
% 0.22/0.52    inference(resolution,[],[f54,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3) | ~m1_subset_1(X4,sK2)) ) | ~spl10_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f68])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4)) | ~spl10_29),
% 0.22/0.52    inference(avatar_component_clause,[],[f311])).
% 0.22/0.52  % (14920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    ~spl10_6 | ~spl10_9 | spl10_30),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f405])).
% 0.22/0.52  % (14912)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  fof(f405,plain,(
% 0.22/0.52    $false | (~spl10_6 | ~spl10_9 | spl10_30)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f324,f403])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k11_relat_1(sK3,X0),k1_zfmisc_1(sK2))) ) | (~spl10_6 | ~spl10_9)),
% 0.22/0.52    inference(superposition,[],[f394,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0] : (k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))) ) | ~spl10_9),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f109,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.52  fof(f394,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK2))) ) | ~spl10_6),
% 0.22/0.52    inference(backward_demodulation,[],[f334,f388])).
% 0.22/0.52  fof(f388,plain,(
% 0.22/0.52    ( ! [X0] : (k7_relset_1(sK1,sK2,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl10_6),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f89,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl10_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k7_relset_1(sK1,sK2,sK3,X0),k1_zfmisc_1(sK2))) ) | ~spl10_6),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f89,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    ~m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2)) | spl10_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f322])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    spl10_30 <=> m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.22/0.52  fof(f325,plain,(
% 0.22/0.52    ~spl10_30 | spl10_18 | ~spl10_29),
% 0.22/0.52    inference(avatar_split_clause,[],[f319,f311,f193,f322])).
% 0.22/0.52  fof(f319,plain,(
% 0.22/0.52    ~m1_subset_1(k11_relat_1(sK3,sK4),k1_zfmisc_1(sK2)) | (spl10_18 | ~spl10_29)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f195,f313,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ~m1_subset_1(sK8(sK3,sK4),sK2) | spl10_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f193])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    spl10_29 | ~spl10_9 | ~spl10_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f298,f187,f107,f311])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    spl10_17 <=> r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    r2_hidden(sK8(sK3,sK4),k11_relat_1(sK3,sK4)) | (~spl10_9 | ~spl10_17)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f109,f189,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3) | ~spl10_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f187])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    spl10_11 | ~spl10_1 | ~spl10_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f266,f250,f64,f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl10_11 <=> r2_hidden(sK4,k1_relat_1(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl10_1 <=> r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.52  fof(f250,plain,(
% 0.22/0.52    spl10_25 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    r2_hidden(sK4,k1_relat_1(sK3)) | (~spl10_1 | ~spl10_25)),
% 0.22/0.52    inference(backward_demodulation,[],[f65,f252])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl10_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f250])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) | ~spl10_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f64])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    ~spl10_11 | spl10_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f220,f115,f124])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl10_10 <=> sP9(sK4,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ~r2_hidden(sK4,k1_relat_1(sK3)) | spl10_10),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f60,f205,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3)) ) | spl10_10),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f116,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | sP9(X5,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f61_D])).
% 0.22/0.52  fof(f61_D,plain,(
% 0.22/0.52    ( ! [X0,X5] : (( ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0) ) <=> ~sP9(X5,X0)) )),
% 0.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~sP9(sK4,sK3) | spl10_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (sP0(X0,k1_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sP0(X0,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.22/0.52    inference(definition_folding,[],[f3,f20])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ~spl10_6 | spl10_12),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    $false | (~spl10_6 | spl10_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f257,f89])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl10_12),
% 0.22/0.52    inference(subsumption_resolution,[],[f248,f60])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    ~sP0(sK3,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl10_12),
% 0.22/0.52    inference(superposition,[],[f131,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~sP0(sK3,k1_relset_1(sK1,sK2,sK3)) | spl10_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl10_12 <=> sP0(sK3,k1_relset_1(sK1,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    spl10_25 | ~spl10_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f246,f87,f250])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl10_6),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f89,f56])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    spl10_17 | ~spl10_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f181,f124,f187])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,sK8(sK3,sK4)),sK3) | ~spl10_11),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f60,f126,f47])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    r2_hidden(sK4,k1_relat_1(sK3)) | ~spl10_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f124])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ~spl10_12 | spl10_1 | ~spl10_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f120,f115,f64,f129])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ~sP0(sK3,k1_relset_1(sK1,sK2,sK3)) | (spl10_1 | ~spl10_10)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f66,f117,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X5,X1] : (~sP9(X5,X0) | ~sP0(X0,X1) | r2_hidden(X5,X1)) )),
% 0.22/0.52    inference(general_splitting,[],[f48,f61_D])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    sP9(sK4,sK3) | ~spl10_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ~r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3)) | spl10_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f64])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    spl10_11 | ~spl10_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f121,f115,f124])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    r2_hidden(sK4,k1_relat_1(sK3)) | ~spl10_10),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f60,f117,f62])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl10_10 | ~spl10_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f72,f115])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl10_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    sP9(sK4,sK3) | ~spl10_3),
% 0.22/0.52    inference(resolution,[],[f61,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl10_9 | ~spl10_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f87,f107])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl10_6),
% 0.22/0.52    inference(resolution,[],[f55,f89])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl10_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f87])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ((((! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))) & ((r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))) & m1_subset_1(sK4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f24,f29,f28,f27,f26,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(sK1,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(sK1,X1,X2))) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(sK1,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(sK1,X1,X2))) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(X3,k1_relset_1(sK1,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,sK2)) | r2_hidden(X3,k1_relset_1(sK1,sK2,X2))) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & ~v1_xboole_0(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(X3,k1_relset_1(sK1,sK2,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,sK2)) | r2_hidden(X3,k1_relset_1(sK1,sK2,X2))) & m1_subset_1(X3,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK3) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(X3,k1_relset_1(sK1,sK2,sK3))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK3) & m1_subset_1(X5,sK2)) | r2_hidden(X3,k1_relset_1(sK1,sK2,sK3))) & m1_subset_1(X3,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),sK3) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(X3,k1_relset_1(sK1,sK2,sK3))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),sK3) & m1_subset_1(X5,sK2)) | r2_hidden(X3,k1_relset_1(sK1,sK2,sK3))) & m1_subset_1(X3,sK1)) => ((! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3) | ~m1_subset_1(X4,sK2)) | ~r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))) & (? [X5] : (r2_hidden(k4_tarski(sK4,X5),sK3) & m1_subset_1(X5,sK2)) | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))) & m1_subset_1(sK4,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X5] : (r2_hidden(k4_tarski(sK4,X5),sK3) & m1_subset_1(X5,sK2)) => (r2_hidden(k4_tarski(sK4,sK5),sK3) & m1_subset_1(sK5,sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X5] : (r2_hidden(k4_tarski(X3,X5),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(rectify,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((! [X4] : (~r2_hidden(k4_tarski(X3,X4),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k1_relset_1(X0,X1,X2))) & (? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k1_relset_1(X0,X1,X2)))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  % (14910)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl10_1 | spl10_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f72,f64])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~spl10_1 | spl10_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f68,f64])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_hidden(k4_tarski(sK4,X4),sK3) | ~m1_subset_1(X4,sK2) | ~r2_hidden(sK4,k1_relset_1(sK1,sK2,sK3))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (14924)------------------------------
% 0.22/0.52  % (14924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14924)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (14924)Memory used [KB]: 10874
% 0.22/0.52  % (14924)Time elapsed: 0.090 s
% 0.22/0.52  % (14924)------------------------------
% 0.22/0.52  % (14924)------------------------------
% 0.22/0.53  % (14922)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (14907)Success in time 0.161 s
%------------------------------------------------------------------------------
