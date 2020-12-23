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
% DateTime   : Thu Dec  3 13:03:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 306 expanded)
%              Number of equality atoms :   39 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f64,f70,f79,f90,f94,f112,f121,f126])).

fof(f126,plain,
    ( ~ spl4_6
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_18
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_15
    | ~ spl4_18
    | spl4_20 ),
    inference(subsumption_resolution,[],[f124,f111])).

fof(f111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f110])).

% (2431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f110,plain,
    ( spl4_18
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f124,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_15
    | spl4_20 ),
    inference(forward_demodulation,[],[f123,f63])).

fof(f63,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_9
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f123,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_6
    | ~ spl4_15
    | spl4_20 ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f51,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_6
  <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f122,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_15
    | spl4_20 ),
    inference(superposition,[],[f120,f93])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f120,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_20
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f121,plain,
    ( ~ spl4_20
    | ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f97,f88,f68,f46,f38,f119])).

fof(f38,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f46,plain,
    ( spl4_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f88,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f97,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f47,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f95,f69])).

fof(f69,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f95,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f89,f39])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f47,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f112,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f98,f88,f68,f38,f110])).

fof(f98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f39,f96])).

fof(f94,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f24,f92])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f90,plain,
    ( spl4_14
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f80,f77,f54,f88])).

fof(f54,plain,
    ( spl4_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f77,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f20,f77])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f70,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f66,f54,f42,f68])).

fof(f42,plain,
    ( spl4_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f66,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f43,f65])).

fof(f65,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f56,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f52,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f48,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f40,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f38])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f16,f27])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (2427)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (2427)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (2438)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f56,f64,f70,f79,f90,f94,f112,f121,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~spl4_6 | ~spl4_9 | ~spl4_15 | ~spl4_18 | spl4_20),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    $false | (~spl4_6 | ~spl4_9 | ~spl4_15 | ~spl4_18 | spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  % (2431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl4_18 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_9 | ~spl4_15 | spl4_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f123,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_9 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_6 | ~spl4_15 | spl4_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_6 <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_15 | spl4_20)),
% 0.21/0.48    inference(superposition,[],[f120,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_15 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl4_20 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~spl4_20 | ~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f88,f68,f46,f38,f119])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl4_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl4_14 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_14)),
% 0.21/0.48    inference(backward_demodulation,[],[f47,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_10 | ~spl4_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_14)),
% 0.21/0.48    inference(resolution,[],[f89,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | ~spl4_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl4_18 | ~spl4_3 | ~spl4_10 | ~spl4_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f88,f68,f38,f110])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_10 | ~spl4_14)),
% 0.21/0.48    inference(backward_demodulation,[],[f39,f96])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f92])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl4_14 | ~spl4_7 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f77,f54,f88])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl4_7 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl4_12 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) ) | (~spl4_7 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f78,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f77])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_10 | ~spl4_4 | ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f54,f42,f68])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl4_4 <=> v1_xboole_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | (~spl4_4 | ~spl4_7)),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | (~spl4_4 | ~spl4_7)),
% 0.21/0.48    inference(resolution,[],[f55,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    v1_xboole_0(sK3) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f50])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f46])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f42])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_xboole_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f38])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(backward_demodulation,[],[f16,f27])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2427)------------------------------
% 0.21/0.48  % (2427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2427)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2427)Memory used [KB]: 10618
% 0.21/0.48  % (2427)Time elapsed: 0.063 s
% 0.21/0.48  % (2427)------------------------------
% 0.21/0.48  % (2427)------------------------------
% 0.21/0.49  % (2417)Success in time 0.119 s
%------------------------------------------------------------------------------
