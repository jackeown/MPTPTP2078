%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  97 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 216 expanded)
%              Number of equality atoms :   31 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f46,f59,f64,f101,f111])).

fof(f111,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_9 ),
    inference(superposition,[],[f80,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_9
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f80,plain,(
    k1_xboole_0 != k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f25,f79])).

fof(f79,plain,(
    ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f25,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,
    ( spl4_9
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f96,f62,f39,f99])).

fof(f39,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( spl4_4
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f96,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f93,plain,
    ( r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | r1_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f32,f83])).

fof(f83,plain,
    ( k1_relat_1(sK3) = k4_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f63])).

fof(f63,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k4_xboole_0(X0,sK1) = X0 ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,sK1)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f34,f47])).

fof(f47,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,
    ( ~ spl4_1
    | spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f60,f56,f62,f39])).

fof(f56,plain,
    ( spl4_3
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f60,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f28,f57])).

fof(f57,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f59,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f39,f56])).

fof(f54,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f31,f53])).

fof(f53,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f43,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f42,f39])).

fof(f37,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:33:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (24361)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (24361)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f44,f46,f59,f64,f101,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~spl4_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    $false | ~spl4_9),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~spl4_9),
% 0.21/0.47    inference(superposition,[],[f80,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    k1_xboole_0 = k7_relat_1(sK3,sK1) | ~spl4_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl4_9 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK3,sK1)),
% 0.21/0.47    inference(superposition,[],[f25,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.21/0.47    inference(resolution,[],[f36,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl4_9 | ~spl4_1 | ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f62,f39,f99])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl4_1 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl4_4 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | k1_xboole_0 = k7_relat_1(sK3,sK1) | ~spl4_4),
% 0.21/0.47    inference(resolution,[],[f93,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    r1_xboole_0(k1_relat_1(sK3),sK1) | ~spl4_4),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    k1_relat_1(sK3) != k1_relat_1(sK3) | r1_xboole_0(k1_relat_1(sK3),sK1) | ~spl4_4),
% 0.21/0.47    inference(superposition,[],[f32,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    k1_relat_1(sK3) = k4_xboole_0(k1_relat_1(sK3),sK1) | ~spl4_4),
% 0.21/0.47    inference(resolution,[],[f52,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,sK2) | k4_xboole_0(X0,sK1) = X0) )),
% 0.21/0.47    inference(resolution,[],[f51,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.47    inference(superposition,[],[f34,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    sK1 = k4_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(resolution,[],[f33,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl4_1 | spl4_4 | ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f56,f62,f39])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl4_3 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~spl4_3),
% 0.21/0.47    inference(superposition,[],[f28,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    sK3 = k7_relat_1(sK3,sK2) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl4_3 | ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f54,f39,f56])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.21/0.47    inference(resolution,[],[f31,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    v4_relat_1(sK3,sK2)),
% 0.21/0.47    inference(resolution,[],[f35,f23])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    $false | spl4_2),
% 0.21/0.47    inference(resolution,[],[f43,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl4_1 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f42,f39])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK3)),
% 0.21/0.47    inference(resolution,[],[f26,f23])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24361)------------------------------
% 0.21/0.47  % (24361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24361)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24361)Memory used [KB]: 10618
% 0.21/0.47  % (24361)Time elapsed: 0.057 s
% 0.21/0.47  % (24361)------------------------------
% 0.21/0.47  % (24361)------------------------------
% 0.21/0.47  % (24348)Success in time 0.112 s
%------------------------------------------------------------------------------
