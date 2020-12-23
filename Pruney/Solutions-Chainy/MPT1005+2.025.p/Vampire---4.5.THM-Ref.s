%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  147 ( 228 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f54,f58,f66,f75,f95,f104,f108,f113])).

fof(f113,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | ~ spl3_15
    | spl3_17
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_15
    | spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f111,f94])).

fof(f94,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f111,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_7
    | spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f110,f53])).

fof(f53,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_7
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

% (21455)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f110,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_5
    | spl3_17
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f109,f45])).

fof(f45,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f109,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_17
    | ~ spl3_18 ),
    inference(superposition,[],[f103,f107])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f103,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_17
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f108,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f23,f106])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f104,plain,
    ( ~ spl3_17
    | ~ spl3_3
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f80,f73,f40,f36,f102])).

fof(f36,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( spl3_4
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f73,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f80,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | ~ spl3_3
    | spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f41,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f41,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f95,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f81,f73,f36,f93])).

fof(f81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f37,f78])).

fof(f75,plain,
    ( spl3_12
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f67,f64,f56,f73])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f64,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f19,f64])).

% (21461)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f17,f56])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f54,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f44])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f42,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

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

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f36])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f14,f25])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:32:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (21469)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (21463)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (21463)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f38,f42,f46,f54,f58,f66,f75,f95,f104,f108,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl3_5 | ~spl3_7 | ~spl3_15 | spl3_17 | ~spl3_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    $false | (~spl3_5 | ~spl3_7 | ~spl3_15 | spl3_17 | ~spl3_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl3_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_5 | ~spl3_7 | spl3_17 | ~spl3_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f110,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  % (21455)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_5 | spl3_17 | ~spl3_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_5 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_17 | ~spl3_18)),
% 0.21/0.48    inference(superposition,[],[f103,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl3_18 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl3_17 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f106])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~spl3_17 | ~spl3_3 | spl3_4 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f73,f40,f36,f102])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_4 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl3_12 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (~spl3_3 | spl3_4 | ~spl3_12)),
% 0.21/0.48    inference(backward_demodulation,[],[f41,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | (~spl3_3 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f74,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_15 | ~spl3_3 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f81,f73,f36,f93])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_12)),
% 0.21/0.48    inference(backward_demodulation,[],[f37,f78])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_12 | ~spl3_8 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f64,f56,f73])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl3_8 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl3_8 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f65,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f64])).
% 0.21/0.48  % (21461)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f56])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f52])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f44])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f40])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_2)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f36])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(backward_demodulation,[],[f14,f25])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21463)------------------------------
% 0.21/0.48  % (21463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21463)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21463)Memory used [KB]: 10618
% 0.21/0.48  % (21463)Time elapsed: 0.063 s
% 0.21/0.48  % (21463)------------------------------
% 0.21/0.48  % (21463)------------------------------
% 0.21/0.49  % (21453)Success in time 0.124 s
%------------------------------------------------------------------------------
