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
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 158 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f76,f84,f91,f99,f107,f114])).

fof(f114,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_8 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_8 ),
    inference(superposition,[],[f106,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f108,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f108,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f106,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_8
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f107,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f101,f96,f56,f104])).

fof(f56,plain,
    ( spl4_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f96,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f101,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f58,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f58,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f99,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f94,f88,f96])).

fof(f88,plain,
    ( spl4_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f90,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f90,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( spl4_6
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f86,f81,f73,f88])).

fof(f73,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f33,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f84,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f79,f61,f81])).

fof(f61,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f63,f54])).

fof(f54,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f76,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f71,f73])).

fof(f71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = sK3(X0) ),
    inference(resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f64,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f59,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (817)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (825)Refutation not found, incomplete strategy% (825)------------------------------
% 0.21/0.52  % (825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (825)Memory used [KB]: 10746
% 0.21/0.52  % (825)Time elapsed: 0.084 s
% 0.21/0.52  % (825)------------------------------
% 0.21/0.52  % (825)------------------------------
% 0.21/0.57  % (811)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (811)Refutation not found, incomplete strategy% (811)------------------------------
% 0.21/0.57  % (811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (811)Memory used [KB]: 10618
% 0.21/0.57  % (811)Time elapsed: 0.128 s
% 0.21/0.57  % (811)------------------------------
% 0.21/0.57  % (811)------------------------------
% 0.21/0.57  % (819)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (819)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f115,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f59,f64,f76,f84,f91,f99,f107,f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    spl4_8),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    $false | spl4_8),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f112])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0 | spl4_8),
% 0.21/0.58    inference(superposition,[],[f106,f111])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f108,f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.58    inference(resolution,[],[f42,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.58    inference(ennf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl4_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f104])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    spl4_8 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ~spl4_8 | spl4_1 | ~spl4_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f101,f96,f56,f104])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    spl4_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    spl4_7 <=> k1_xboole_0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl4_1 | ~spl4_7)),
% 0.21/0.58    inference(backward_demodulation,[],[f58,f98])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl4_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f96])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f56])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    spl4_7 | ~spl4_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f94,f88,f96])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    spl4_6 <=> v1_xboole_0(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl4_6),
% 0.21/0.58    inference(resolution,[],[f90,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    v1_xboole_0(sK2) | ~spl4_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f88])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    spl4_6 | ~spl4_4 | ~spl4_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f86,f81,f73,f88])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.58  fof(f86,plain,(
% 0.21/0.58    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2) | ~spl4_5),
% 0.21/0.58    inference(resolution,[],[f33,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f81])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    spl4_5 | ~spl4_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f79,f61,f81])).
% 0.21/0.58  fof(f61,plain,(
% 0.21/0.58    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.21/0.58    inference(forward_demodulation,[],[f63,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f61])).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    spl4_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f71,f73])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(backward_demodulation,[],[f35,f70])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = sK3(X0)) )),
% 0.21/0.58    inference(resolution,[],[f32,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    spl4_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f26,f61])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.21/0.58    inference(ennf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.58    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.58  fof(f18,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.58    inference(negated_conjecture,[],[f17])).
% 0.21/0.58  fof(f17,conjecture,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ~spl4_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f27,f56])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (819)------------------------------
% 0.21/0.58  % (819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (819)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (819)Memory used [KB]: 10746
% 0.21/0.58  % (819)Time elapsed: 0.131 s
% 0.21/0.58  % (819)------------------------------
% 0.21/0.58  % (819)------------------------------
% 1.45/0.58  % (802)Success in time 0.201 s
%------------------------------------------------------------------------------
