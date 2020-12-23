%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 192 expanded)
%              Number of leaves         :   31 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  409 ( 688 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f89,f95,f98,f102,f131,f136,f154,f165,f166,f174,f188,f192])).

fof(f192,plain,
    ( ~ spl9_5
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl9_5
    | spl9_15 ),
    inference(subsumption_resolution,[],[f88,f189])).

fof(f189,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl9_15 ),
    inference(resolution,[],[f187,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f187,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl9_15
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f188,plain,
    ( ~ spl9_8
    | ~ spl9_15
    | ~ spl9_6
    | ~ spl9_11
    | spl9_14 ),
    inference(avatar_split_clause,[],[f184,f172,f159,f93,f186,f126])).

% (11843)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (11854)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f126,plain,
    ( spl9_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f93,plain,
    ( spl9_6
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f159,plain,
    ( spl9_11
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f172,plain,
    ( spl9_14
  <=> m1_subset_1(sK8(sK3,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f184,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_11
    | spl9_14 ),
    inference(forward_demodulation,[],[f183,f160])).

fof(f160,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f183,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | spl9_14 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl9_14 ),
    inference(resolution,[],[f181,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f181,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK8(sK3,sK1,sK2),k1_relat_1(X1))
        | ~ v4_relat_1(X1,sK1)
        | ~ v1_relat_1(X1) )
    | spl9_14 ),
    inference(resolution,[],[f178,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f178,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r2_hidden(sK8(sK3,sK1,sK2),X0) )
    | spl9_14 ),
    inference(resolution,[],[f177,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK8(sK3,sK1,sK2),X0) )
    | spl9_14 ),
    inference(resolution,[],[f173,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f173,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK2),sK1)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( ~ spl9_14
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f170,f163,f129,f172])).

fof(f129,plain,
    ( spl9_9
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f163,plain,
    ( spl9_12
  <=> r2_hidden(sK3,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK8(sK3,sK1,sK2),sK1)
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(resolution,[],[f164,f130])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f164,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f166,plain,
    ( ~ spl9_5
    | spl9_11
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f157,f152,f159,f87])).

fof(f152,plain,
    ( spl9_10
  <=> k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f157,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_10 ),
    inference(superposition,[],[f62,f153])).

fof(f153,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f165,plain,
    ( spl9_12
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f156,f152,f71,f163])).

fof(f71,plain,
    ( spl9_1
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f156,plain,
    ( r2_hidden(sK3,k9_relat_1(sK2,sK1))
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(superposition,[],[f77,f153])).

fof(f77,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f154,plain,
    ( spl9_10
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f150,f87,f152])).

fof(f150,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)
    | ~ spl9_5 ),
    inference(resolution,[],[f147,f88])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f64,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f136,plain,
    ( ~ spl9_5
    | spl9_8 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl9_5
    | spl9_8 ),
    inference(subsumption_resolution,[],[f88,f133])).

fof(f133,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl9_8 ),
    inference(resolution,[],[f132,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | spl9_8 ),
    inference(resolution,[],[f127,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f131,plain,
    ( ~ spl9_8
    | spl9_9
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f124,f74,f129,f126])).

fof(f74,plain,
    ( spl9_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k9_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ m1_subset_1(sK8(sK3,X0,sK2),sK1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,
    ( ~ spl9_5
    | spl9_6
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f100,f71,f93,f87])).

fof(f100,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_1 ),
    inference(superposition,[],[f77,f62])).

fof(f98,plain,
    ( ~ spl9_3
    | spl9_6 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl9_3
    | spl9_6 ),
    inference(subsumption_resolution,[],[f80,f96])).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3),sK2)
    | spl9_6 ),
    inference(resolution,[],[f94,f68])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f94,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl9_3
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f95,plain,
    ( ~ spl9_5
    | ~ spl9_6
    | spl9_1 ),
    inference(avatar_split_clause,[],[f90,f71,f93,f87])).

fof(f90,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl9_1 ),
    inference(superposition,[],[f72,f62])).

fof(f72,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f89,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,X1) )
              | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,X1) )
              | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK3),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),X2)
                & m1_subset_1(X5,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                | ~ m1_subset_1(X4,X1) )
            | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) )
            | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
        <~> ? [X4] :
              ( r2_hidden(k4_tarski(X4,X3),X2)
              & m1_subset_1(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ! [X3] :
            ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
          <=> ? [X4] :
                ( r2_hidden(k4_tarski(X4,X3),X2)
                & m1_subset_1(X4,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f81,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f46,f79,f71])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f47,f74,f71])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (11856)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (11850)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (11842)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (11844)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (11856)Refutation not found, incomplete strategy% (11856)------------------------------
% 0.22/0.49  % (11856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (11856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (11856)Memory used [KB]: 10618
% 0.22/0.49  % (11856)Time elapsed: 0.069 s
% 0.22/0.49  % (11856)------------------------------
% 0.22/0.49  % (11856)------------------------------
% 0.22/0.49  % (11842)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (11837)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f76,f81,f89,f95,f98,f102,f131,f136,f154,f165,f166,f174,f188,f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    ~spl9_5 | spl9_15),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    $false | (~spl9_5 | spl9_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f189])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl9_15),
% 0.22/0.49    inference(resolution,[],[f187,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,sK1) | spl9_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f186])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    spl9_15 <=> v4_relat_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl9_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    spl9_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~spl9_8 | ~spl9_15 | ~spl9_6 | ~spl9_11 | spl9_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f184,f172,f159,f93,f186,f126])).
% 0.22/0.49  % (11843)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (11854)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl9_8 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl9_6 <=> r2_hidden(sK3,k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl9_11 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    spl9_14 <=> m1_subset_1(sK8(sK3,sK1,sK2),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl9_11 | spl9_14)),
% 0.22/0.49    inference(forward_demodulation,[],[f183,f160])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~spl9_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f159])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | spl9_14),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl9_14),
% 0.22/0.49    inference(resolution,[],[f181,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(rectify,[],[f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(sK8(sK3,sK1,sK2),k1_relat_1(X1)) | ~v4_relat_1(X1,sK1) | ~v1_relat_1(X1)) ) | spl9_14),
% 0.22/0.49    inference(resolution,[],[f178,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK8(sK3,sK1,sK2),X0)) ) | spl9_14),
% 0.22/0.49    inference(resolution,[],[f177,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK8(sK3,sK1,sK2),X0)) ) | spl9_14),
% 0.22/0.49    inference(resolution,[],[f173,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ~m1_subset_1(sK8(sK3,sK1,sK2),sK1) | spl9_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f172])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ~spl9_14 | ~spl9_9 | ~spl9_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f170,f163,f129,f172])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl9_9 <=> ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    spl9_12 <=> r2_hidden(sK3,k9_relat_1(sK2,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~m1_subset_1(sK8(sK3,sK1,sK2),sK1) | (~spl9_9 | ~spl9_12)),
% 0.22/0.49    inference(resolution,[],[f164,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1)) ) | ~spl9_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f129])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | ~spl9_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f163])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ~spl9_5 | spl9_11 | ~spl9_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f157,f152,f159,f87])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl9_10 <=> k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl9_10),
% 0.22/0.49    inference(superposition,[],[f62,f153])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) | ~spl9_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl9_12 | ~spl9_1 | ~spl9_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f156,f152,f71,f163])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl9_1 <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    r2_hidden(sK3,k9_relat_1(sK2,sK1)) | (~spl9_1 | ~spl9_10)),
% 0.22/0.49    inference(superposition,[],[f77,f153])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | ~spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl9_10 | ~spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f150,f87,f152])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) | ~spl9_5),
% 0.22/0.49    inference(resolution,[],[f147,f88])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f144])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(superposition,[],[f64,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~spl9_5 | spl9_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    $false | (~spl9_5 | spl9_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f133])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl9_8),
% 0.22/0.49    inference(resolution,[],[f132,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | spl9_8),
% 0.22/0.49    inference(resolution,[],[f127,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl9_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ~spl9_8 | spl9_9 | ~spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f124,f74,f129,f126])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl9_2 <=> ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK3,k9_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~m1_subset_1(sK8(sK3,X0,sK2),sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(resolution,[],[f59,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f43])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~spl9_5 | spl9_6 | ~spl9_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f100,f71,f93,f87])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl9_1),
% 0.22/0.49    inference(superposition,[],[f77,f62])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~spl9_3 | spl9_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f97])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    $false | (~spl9_3 | spl9_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f80,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3),sK2)) ) | spl9_6),
% 0.22/0.49    inference(resolution,[],[f94,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f34,f37,f36,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | spl9_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK4,sK3),sK2) | ~spl9_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl9_3 <=> r2_hidden(k4_tarski(sK4,sK3),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~spl9_5 | ~spl9_6 | spl9_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f71,f93,f87])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl9_1),
% 0.22/0.49    inference(superposition,[],[f72,f62])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) | spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl9_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f87])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & ((r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f30,f29,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(X3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)))) => ((! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1)) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) & (? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X5] : (r2_hidden(k4_tarski(X5,sK3),sK2) & m1_subset_1(X5,sK1)) => (r2_hidden(k4_tarski(sK4,sK3),sK2) & m1_subset_1(sK4,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X5] : (r2_hidden(k4_tarski(X5,X3),X2) & m1_subset_1(X5,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.49    inference(rectify,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : ((! [X4] : (~r2_hidden(k4_tarski(X4,X3),X2) | ~m1_subset_1(X4,X1)) | ~r2_hidden(X3,k2_relset_1(X1,X0,X2))) & (? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1)) | r2_hidden(X3,k2_relset_1(X1,X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ! [X3] : (r2_hidden(X3,k2_relset_1(X1,X0,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X4,X3),X2) & m1_subset_1(X4,X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl9_1 | spl9_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f79,f71])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK4,sK3),sK2) | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~spl9_1 | spl9_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f74,f71])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2) | ~m1_subset_1(X4,sK1) | ~r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (11842)------------------------------
% 0.22/0.49  % (11842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (11842)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (11842)Memory used [KB]: 10746
% 0.22/0.49  % (11842)Time elapsed: 0.015 s
% 0.22/0.49  % (11842)------------------------------
% 0.22/0.49  % (11842)------------------------------
% 0.22/0.49  % (11840)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (11832)Success in time 0.13 s
%------------------------------------------------------------------------------
