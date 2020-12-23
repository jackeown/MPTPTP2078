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
% DateTime   : Thu Dec  3 13:02:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 597 expanded)
%              Number of leaves         :   34 ( 168 expanded)
%              Depth                    :   18
%              Number of atoms          :  645 (3013 expanded)
%              Number of equality atoms :  120 ( 443 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f121,f129,f138,f157,f165,f329,f446,f475,f650,f663,f672,f681,f824])).

fof(f824,plain,
    ( ~ spl8_5
    | ~ spl8_7
    | ~ spl8_11
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_11
    | spl8_14 ),
    inference(subsumption_resolution,[],[f822,f186])).

fof(f186,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f141,f185])).

fof(f185,plain,
    ( ! [X0] : sP0(X0,k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f184,f128])).

fof(f128,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f184,plain,
    ( ! [X0] :
        ( sP0(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f183,f156])).

fof(f156,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl8_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f183,plain,(
    ! [X0] :
      ( sP0(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f182,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f182,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | sP0(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f78,f63])).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f141,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f76,f62])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f822,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl8_11
    | spl8_14 ),
    inference(forward_demodulation,[],[f328,f242])).

fof(f242,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f328,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK5,sK4)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl8_14
  <=> v1_funct_2(k1_xboole_0,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f681,plain,
    ( ~ spl8_13
    | spl8_3 ),
    inference(avatar_split_clause,[],[f680,f111,f322])).

fof(f322,plain,
    ( spl8_13
  <=> k1_xboole_0 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f111,plain,
    ( spl8_3
  <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f680,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f679,f130])).

fof(f130,plain,(
    v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,
    ( v1_relat_1(sK6)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
      | ~ v1_funct_1(k2_funct_1(sK6)) )
    & sK5 = k2_relset_1(sK4,sK5,sK6)
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
        | ~ v1_funct_1(k2_funct_1(sK6)) )
      & sK5 = k2_relset_1(sK4,sK5,sK6)
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f679,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f678,f56])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f678,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f677,f59])).

fof(f59,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f677,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f502,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f502,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | k1_xboole_0 != k1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_3 ),
    inference(superposition,[],[f113,f206])).

fof(f206,plain,(
    ! [X3] :
      ( k1_xboole_0 = k2_funct_1(X3)
      | k1_xboole_0 != k1_relat_1(X3)
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f201,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f201,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_relat_1(X3)
      | k1_xboole_0 = k2_funct_1(X3)
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v2_funct_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f67,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

% (12929)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f113,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f672,plain,
    ( ~ spl8_11
    | spl8_13 ),
    inference(avatar_split_clause,[],[f367,f322,f241])).

fof(f367,plain,
    ( k1_xboole_0 != sK5
    | spl8_13 ),
    inference(superposition,[],[f366,f226])).

fof(f226,plain,(
    sK5 = k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f224,f58])).

fof(f224,plain,
    ( sK5 = k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f82,f60])).

fof(f60,plain,(
    sK5 = k2_relset_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f366,plain,
    ( k1_xboole_0 != k2_relat_1(sK6)
    | spl8_13 ),
    inference(subsumption_resolution,[],[f365,f130])).

fof(f365,plain,
    ( ~ v1_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(sK6)
    | spl8_13 ),
    inference(subsumption_resolution,[],[f364,f56])).

fof(f364,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(sK6)
    | spl8_13 ),
    inference(subsumption_resolution,[],[f346,f59])).

fof(f346,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(sK6)
    | spl8_13 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_xboole_0 != k2_relat_1(sK6)
    | spl8_13 ),
    inference(superposition,[],[f324,f291])).

fof(f291,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f289,f63])).

fof(f289,plain,(
    ! [X1] :
      ( k2_relat_1(k1_xboole_0) = k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X1] :
      ( k2_relat_1(k1_xboole_0) = k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k2_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f72,f198])).

fof(f198,plain,(
    ! [X6] :
      ( k1_xboole_0 = k2_funct_1(X6)
      | k1_xboole_0 != k2_relat_1(X6)
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f196,f69])).

fof(f196,plain,(
    ! [X6] :
      ( k1_xboole_0 != k2_relat_1(X6)
      | k1_xboole_0 = k2_funct_1(X6)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f66,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f324,plain,
    ( k1_xboole_0 != k1_relat_1(sK6)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f322])).

fof(f663,plain,
    ( spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f660,f443,f241])).

fof(f443,plain,
    ( spl8_16
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f660,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_16 ),
    inference(resolution,[],[f445,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f445,plain,
    ( sP1(sK4,sK5)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f443])).

fof(f650,plain,
    ( spl8_3
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | spl8_3
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f639,f493])).

fof(f493,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f492,f130])).

fof(f492,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f491,f56])).

fof(f491,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f458,f59])).

fof(f458,plain,
    ( sP0(sK4,k2_funct_1(sK6))
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl8_15 ),
    inference(superposition,[],[f203,f441])).

fof(f441,plain,
    ( sK4 = k1_relat_1(sK6)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl8_15
  <=> sK4 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f203,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f202,f69])).

fof(f202,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f199,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f199,plain,(
    ! [X0] :
      ( sP0(k1_relat_1(X0),k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f181,f72])).

fof(f181,plain,(
    ! [X0] :
      ( sP0(k2_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f639,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl8_3 ),
    inference(resolution,[],[f638,f113])).

fof(f638,plain,(
    ! [X5] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5)))
      | ~ sP0(X5,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f637,f130])).

fof(f637,plain,(
    ! [X5] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5)))
      | ~ sP0(X5,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f636,f56])).

fof(f636,plain,(
    ! [X5] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5)))
      | ~ sP0(X5,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f630,f59])).

fof(f630,plain,(
    ! [X5] :
      ( m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5)))
      | ~ sP0(X5,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f195,f226])).

fof(f195,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5)))
      | ~ sP0(X5,k2_funct_1(X4))
      | ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f77,f71])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f475,plain,
    ( spl8_2
    | ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl8_2
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f473,f130])).

fof(f473,plain,
    ( ~ v1_relat_1(sK6)
    | spl8_2
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f472,f56])).

fof(f472,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_2
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f471,f59])).

fof(f471,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_2
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f458,f384])).

fof(f384,plain,
    ( ~ sP0(sK4,k2_funct_1(sK6))
    | spl8_2 ),
    inference(resolution,[],[f383,f109])).

fof(f109,plain,
    ( ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_2
  <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f383,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6)) ) ),
    inference(subsumption_resolution,[],[f382,f130])).

fof(f382,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f381,f56])).

fof(f381,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(subsumption_resolution,[],[f373,f59])).

fof(f373,plain,(
    ! [X3] :
      ( v1_funct_2(k2_funct_1(sK6),sK5,X3)
      | ~ sP0(X3,k2_funct_1(sK6))
      | ~ v2_funct_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(superposition,[],[f197,f226])).

fof(f197,plain,(
    ! [X8,X7] :
      ( v1_funct_2(k2_funct_1(X7),k2_relat_1(X7),X8)
      | ~ sP0(X8,k2_funct_1(X7))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f76,f71])).

fof(f446,plain,
    ( spl8_15
    | spl8_16 ),
    inference(avatar_split_clause,[],[f437,f443,f439])).

fof(f437,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f434,f57])).

fof(f57,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f434,plain,
    ( ~ v1_funct_2(sK6,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK6) ),
    inference(resolution,[],[f277,f58])).

fof(f277,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f275,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f42,f41,f40])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f275,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f86,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f329,plain,
    ( ~ spl8_13
    | ~ spl8_14
    | spl8_2 ),
    inference(avatar_split_clause,[],[f320,f107,f326,f322])).

fof(f320,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK5,sK4)
    | k1_xboole_0 != k1_relat_1(sK6)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f319,f130])).

fof(f319,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK5,sK4)
    | k1_xboole_0 != k1_relat_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f318,f56])).

fof(f318,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK5,sK4)
    | k1_xboole_0 != k1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f308,f59])).

fof(f308,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK5,sK4)
    | k1_xboole_0 != k1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_2 ),
    inference(superposition,[],[f109,f206])).

fof(f165,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f159,f93])).

fof(f93,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( v2_funct_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v2_funct_1(sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_1)).

fof(f159,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl8_6 ),
    inference(resolution,[],[f152,f94])).

fof(f94,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_6
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f157,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f149,f154,f151])).

fof(f149,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f73,f65])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f138,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f93,f124])).

fof(f124,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_4
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f129,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f118,f126,f123])).

fof(f118,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f68,f65])).

fof(f121,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f120])).

% (12927)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f120,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f119,f74])).

fof(f119,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f117,f116])).

fof(f116,plain,
    ( ~ v1_relat_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f115,f56])).

fof(f115,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl8_1 ),
    inference(resolution,[],[f70,f105])).

fof(f105,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_1
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f114,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f61,f111,f107,f103])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(k2_funct_1(sK6),sK5,sK4)
    | ~ v1_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (12931)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (12923)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (12939)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (12925)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (12933)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (12943)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (12920)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (12934)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (12921)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (12919)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (12926)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (12937)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (12923)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f825,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f114,f121,f129,f138,f157,f165,f329,f446,f475,f650,f663,f672,f681,f824])).
% 0.21/0.52  fof(f824,plain,(
% 0.21/0.52    ~spl8_5 | ~spl8_7 | ~spl8_11 | spl8_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f823])).
% 0.21/0.52  fof(f823,plain,(
% 0.21/0.52    $false | (~spl8_5 | ~spl8_7 | ~spl8_11 | spl8_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f822,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl8_5 | ~spl8_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(X0,k1_xboole_0)) ) | (~spl8_5 | ~spl8_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f184,f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0) | ~spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl8_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f183,f156])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    v1_funct_1(k1_xboole_0) | ~spl8_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl8_7 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | sP0(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f78,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(definition_folding,[],[f31,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f76,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f38])).
% 0.21/0.52  fof(f822,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK4) | (~spl8_11 | spl8_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f328,f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    k1_xboole_0 = sK5 | ~spl8_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f241])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    spl8_11 <=> k1_xboole_0 = sK5),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK5,sK4) | spl8_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f326])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    spl8_14 <=> v1_funct_2(k1_xboole_0,sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.52  fof(f681,plain,(
% 0.21/0.52    ~spl8_13 | spl8_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f680,f111,f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl8_13 <=> k1_xboole_0 = k1_relat_1(sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl8_3 <=> m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f680,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK6) | spl8_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f679,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    v1_relat_1(sK6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    v1_relat_1(sK6) | ~v1_relat_1(k2_zfmisc_1(sK4,sK5))),
% 0.21/0.52    inference(resolution,[],[f68,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    (~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))) & sK5 = k2_relset_1(sK4,sK5,sK6) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f679,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK6) | ~v1_relat_1(sK6) | spl8_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f678,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    v1_funct_1(sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f678,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f677,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    v2_funct_1(sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f677,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f502,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f502,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | k1_xboole_0 != k1_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_3),
% 0.21/0.52    inference(superposition,[],[f113,f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    ( ! [X3] : (k1_xboole_0 = k2_funct_1(X3) | k1_xboole_0 != k1_relat_1(X3) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f201,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ( ! [X3] : (k1_xboole_0 != k1_relat_1(X3) | k1_xboole_0 = k2_funct_1(X3) | ~v1_relat_1(k2_funct_1(X3)) | ~v2_funct_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.21/0.52    inference(superposition,[],[f67,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  % (12929)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f111])).
% 0.21/0.52  fof(f672,plain,(
% 0.21/0.52    ~spl8_11 | spl8_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f367,f322,f241])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    k1_xboole_0 != sK5 | spl8_13),
% 0.21/0.52    inference(superposition,[],[f366,f226])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    sK5 = k2_relat_1(sK6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f224,f58])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    sK5 = k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.52    inference(superposition,[],[f82,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    sK5 = k2_relset_1(sK4,sK5,sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f365,f130])).
% 0.21/0.52  fof(f365,plain,(
% 0.21/0.52    ~v1_relat_1(sK6) | k1_xboole_0 != k2_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f364,f56])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | k1_xboole_0 != k2_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f59])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | k1_xboole_0 != k2_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f345])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | k1_xboole_0 != k2_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(superposition,[],[f324,f291])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_xboole_0 != k2_relat_1(X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f289,f63])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_xboole_0 != k2_relat_1(X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f280])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_xboole_0 != k2_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(superposition,[],[f72,f198])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ( ! [X6] : (k1_xboole_0 = k2_funct_1(X6) | k1_xboole_0 != k2_relat_1(X6) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f69])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X6] : (k1_xboole_0 != k2_relat_1(X6) | k1_xboole_0 = k2_funct_1(X6) | ~v1_relat_1(k2_funct_1(X6)) | ~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.21/0.52    inference(superposition,[],[f66,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK6) | spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f322])).
% 0.21/0.52  fof(f663,plain,(
% 0.21/0.52    spl8_11 | ~spl8_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f660,f443,f241])).
% 0.21/0.52  fof(f443,plain,(
% 0.21/0.52    spl8_16 <=> sP1(sK4,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.52  fof(f660,plain,(
% 0.21/0.52    k1_xboole_0 = sK5 | ~spl8_16),
% 0.21/0.52    inference(resolution,[],[f445,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f445,plain,(
% 0.21/0.52    sP1(sK4,sK5) | ~spl8_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f443])).
% 0.21/0.52  fof(f650,plain,(
% 0.21/0.52    spl8_3 | ~spl8_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f649])).
% 0.21/0.52  fof(f649,plain,(
% 0.21/0.52    $false | (spl8_3 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f639,f493])).
% 0.21/0.52  fof(f493,plain,(
% 0.21/0.52    sP0(sK4,k2_funct_1(sK6)) | ~spl8_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f492,f130])).
% 0.21/0.52  fof(f492,plain,(
% 0.21/0.52    sP0(sK4,k2_funct_1(sK6)) | ~v1_relat_1(sK6) | ~spl8_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f491,f56])).
% 0.21/0.52  fof(f491,plain,(
% 0.21/0.52    sP0(sK4,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl8_15),
% 0.21/0.52    inference(subsumption_resolution,[],[f458,f59])).
% 0.21/0.52  fof(f458,plain,(
% 0.21/0.52    sP0(sK4,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~spl8_15),
% 0.21/0.52    inference(superposition,[],[f203,f441])).
% 0.21/0.52  fof(f441,plain,(
% 0.21/0.52    sK4 = k1_relat_1(sK6) | ~spl8_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f439])).
% 0.21/0.52  fof(f439,plain,(
% 0.21/0.52    spl8_15 <=> sK4 = k1_relat_1(sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f202,f69])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k1_relat_1(X0),k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f181,f72])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X0] : (sP0(k2_relat_1(X0),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f78,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f639,plain,(
% 0.21/0.52    ~sP0(sK4,k2_funct_1(sK6)) | spl8_3),
% 0.21/0.52    inference(resolution,[],[f638,f113])).
% 0.21/0.52  fof(f638,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5))) | ~sP0(X5,k2_funct_1(sK6))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f637,f130])).
% 0.21/0.52  fof(f637,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5))) | ~sP0(X5,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f636,f56])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5))) | ~sP0(X5,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f630,f59])).
% 0.21/0.52  fof(f630,plain,(
% 0.21/0.52    ( ! [X5] : (m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,X5))) | ~sP0(X5,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(superposition,[],[f195,f226])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k2_funct_1(X4),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X4),X5))) | ~sP0(X5,k2_funct_1(X4)) | ~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.52    inference(superposition,[],[f77,f71])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    spl8_2 | ~spl8_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f474])).
% 0.21/0.52  fof(f474,plain,(
% 0.21/0.52    $false | (spl8_2 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f473,f130])).
% 0.21/0.52  fof(f473,plain,(
% 0.21/0.52    ~v1_relat_1(sK6) | (spl8_2 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f472,f56])).
% 0.21/0.52  fof(f472,plain,(
% 0.21/0.52    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl8_2 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f471,f59])).
% 0.21/0.52  fof(f471,plain,(
% 0.21/0.52    ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | (spl8_2 | ~spl8_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f458,f384])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    ~sP0(sK4,k2_funct_1(sK6)) | spl8_2),
% 0.21/0.52    inference(resolution,[],[f383,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl8_2 <=> v1_funct_2(k2_funct_1(sK6),sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f383,plain,(
% 0.21/0.52    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f382,f130])).
% 0.21/0.52  fof(f382,plain,(
% 0.21/0.52    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f381,f56])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f373,f59])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    ( ! [X3] : (v1_funct_2(k2_funct_1(sK6),sK5,X3) | ~sP0(X3,k2_funct_1(sK6)) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) )),
% 0.21/0.52    inference(superposition,[],[f197,f226])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ( ! [X8,X7] : (v1_funct_2(k2_funct_1(X7),k2_relat_1(X7),X8) | ~sP0(X8,k2_funct_1(X7)) | ~v2_funct_1(X7) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.21/0.52    inference(superposition,[],[f76,f71])).
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    spl8_15 | spl8_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f437,f443,f439])).
% 0.21/0.52  fof(f437,plain,(
% 0.21/0.52    sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f434,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    v1_funct_2(sK6,sK4,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f434,plain,(
% 0.21/0.52    ~v1_funct_2(sK6,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relat_1(sK6)),
% 0.21/0.52    inference(resolution,[],[f277,f58])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f275,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f35,f42,f41,f40])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.52    inference(superposition,[],[f86,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f41])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ~spl8_13 | ~spl8_14 | spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f320,f107,f326,f322])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK5,sK4) | k1_xboole_0 != k1_relat_1(sK6) | spl8_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f319,f130])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK5,sK4) | k1_xboole_0 != k1_relat_1(sK6) | ~v1_relat_1(sK6) | spl8_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f318,f56])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK5,sK4) | k1_xboole_0 != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f308,f59])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,sK5,sK4) | k1_xboole_0 != k1_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_2),
% 0.21/0.52    inference(superposition,[],[f109,f206])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl8_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    $false | ~spl8_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    v1_relat_1(sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    v2_funct_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ? [X0] : (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_1)).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~v1_relat_1(sK7) | ~spl8_6),
% 0.21/0.52    inference(resolution,[],[f152,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    v1_funct_1(sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f55])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl8_6 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl8_6 | spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f149,f154,f151])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f73,f65])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ~spl8_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    $false | ~spl8_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl8_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl8_4 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl8_4 | spl8_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f118,f126,f123])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f68,f65])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl8_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.52  % (12927)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    $false | spl8_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f74])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~v1_relat_1(k2_zfmisc_1(sK4,sK5)) | spl8_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ~v1_relat_1(sK6) | spl8_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f115,f56])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl8_1),
% 0.21/0.52    inference(resolution,[],[f70,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~v1_funct_1(k2_funct_1(sK6)) | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl8_1 <=> v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f61,f111,f107,f103])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~m1_subset_1(k2_funct_1(sK6),k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(k2_funct_1(sK6),sK5,sK4) | ~v1_funct_1(k2_funct_1(sK6))),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12923)------------------------------
% 0.21/0.52  % (12923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12923)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12923)Memory used [KB]: 6396
% 0.21/0.52  % (12923)Time elapsed: 0.105 s
% 0.21/0.52  % (12923)------------------------------
% 0.21/0.52  % (12923)------------------------------
% 0.21/0.52  % (12942)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (12916)Success in time 0.168 s
%------------------------------------------------------------------------------
