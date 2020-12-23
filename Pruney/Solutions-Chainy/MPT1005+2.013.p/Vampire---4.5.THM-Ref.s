%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 265 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f48,f52,f56,f60,f64,f70,f76,f87,f98,f122,f127])).

fof(f127,plain,
    ( spl3_14
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_14
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_14
    | ~ spl3_18 ),
    inference(superposition,[],[f97,f121])).

fof(f121,plain,
    ( ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_18
  <=> ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f97,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_14
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f122,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f118,f84,f62,f50,f30,f120])).

fof(f30,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f84,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f118,plain,
    ( ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f117,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f117,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f115,f86])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f115,plain,
    ( ! [X0] : k7_relset_1(k1_xboole_0,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f32])).

fof(f32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f63,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f98,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f90,f84,f25,f95])).

fof(f25,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_1
    | ~ spl3_13 ),
    inference(superposition,[],[f27,f86])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f87,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f78,f73,f54,f84])).

fof(f54,plain,
    ( spl3_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f73,plain,
    ( spl3_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f75,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f76,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f71,f68,f30,f73])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f71,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f32])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f66,f58,f45,f68])).

fof(f45,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f59,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

% (7510)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f56,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

% (7504)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:03:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (7505)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  % (7505)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f128,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f28,f33,f48,f52,f56,f60,f64,f70,f76,f87,f98,f122,f127])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    spl3_14 | ~spl3_18),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    $false | (spl3_14 | ~spl3_18)),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f125])).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    k1_xboole_0 != k1_xboole_0 | (spl3_14 | ~spl3_18)),
% 0.22/0.45    inference(superposition,[],[f97,f121])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) ) | ~spl3_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f120])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    spl3_18 <=> ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.45  fof(f97,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f95])).
% 0.22/0.45  fof(f95,plain,(
% 0.22/0.45    spl3_14 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    spl3_18 | ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f118,f84,f62,f50,f30,f120])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl3_6 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_9 <=> ! [X1,X3,X0,X2] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl3_13 <=> k1_xboole_0 = sK2),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) ) | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_13)),
% 0.22/0.45    inference(forward_demodulation,[],[f117,f51])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) ) | (~spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.22/0.45    inference(forward_demodulation,[],[f115,f86])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    k1_xboole_0 = sK2 | ~spl3_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f84])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    ( ! [X0] : (k7_relset_1(k1_xboole_0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | (~spl3_2 | ~spl3_9)),
% 0.22/0.45    inference(resolution,[],[f63,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f30])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f62])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    ~spl3_14 | spl3_1 | ~spl3_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f90,f84,f25,f95])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    spl3_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl3_1 | ~spl3_13)),
% 0.22/0.45    inference(superposition,[],[f27,f86])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f25])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    spl3_13 | ~spl3_7 | ~spl3_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f78,f73,f54,f84])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl3_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl3_11 <=> v1_xboole_0(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    k1_xboole_0 = sK2 | (~spl3_7 | ~spl3_11)),
% 0.22/0.45    inference(resolution,[],[f75,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f54])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    v1_xboole_0(sK2) | ~spl3_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl3_11 | ~spl3_2 | ~spl3_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f71,f68,f30,f73])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl3_10 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    v1_xboole_0(sK2) | (~spl3_2 | ~spl3_10)),
% 0.22/0.45    inference(resolution,[],[f69,f32])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl3_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl3_10 | ~spl3_5 | ~spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f66,f58,f45,f68])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl3_8 <=> ! [X1,X0,X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | (~spl3_5 | ~spl3_8)),
% 0.22/0.45    inference(resolution,[],[f59,f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f45])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f62])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f58])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  % (7510)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f54])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f45])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  % (7504)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f18,f25])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7505)------------------------------
% 0.22/0.45  % (7505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7505)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7505)Memory used [KB]: 10618
% 0.22/0.45  % (7505)Time elapsed: 0.006 s
% 0.22/0.45  % (7505)------------------------------
% 0.22/0.45  % (7505)------------------------------
% 0.22/0.45  % (7511)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.45  % (7499)Success in time 0.087 s
%------------------------------------------------------------------------------
