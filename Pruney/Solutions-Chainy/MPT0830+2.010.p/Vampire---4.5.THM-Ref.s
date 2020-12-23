%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 124 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 287 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f75,f77,f80,f84,f89,f91,f100,f103,f109])).

fof(f109,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f99,f45])).

fof(f45,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f99,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_9
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f103,plain,
    ( ~ spl4_4
    | spl4_5
    | spl4_8 ),
    inference(avatar_split_clause,[],[f101,f87,f69,f66])).

fof(f66,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f69,plain,
    ( spl4_5
  <=> ! [X0] : ~ v4_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f87,plain,
    ( spl4_8
  <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_8 ),
    inference(resolution,[],[f88,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f88,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f100,plain,
    ( ~ spl4_4
    | ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f96,f82,f98,f66])).

fof(f82,plain,
    ( spl4_7
  <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(resolution,[],[f83,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f83,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f91,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl4_6 ),
    inference(resolution,[],[f74,f45])).

fof(f74,plain,
    ( ! [X1] : ~ v5_relat_1(sK3,X1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_6
  <=> ! [X1] : ~ v5_relat_1(sK3,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f89,plain,
    ( ~ spl4_8
    | ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f85,f60,f54,f87])).

fof(f54,plain,
    ( spl4_1
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( spl4_3
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_3 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f61,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f84,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f78,f57,f54,f82])).

fof(f57,plain,
    ( spl4_2
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_2 ),
    inference(resolution,[],[f58,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f58,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f80,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f30,f23])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ~ spl4_4
    | spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f64,f54,f73,f66])).

fof(f64,plain,
    ( ! [X1] :
        ( ~ v5_relat_1(sK3,X1)
        | ~ v1_relat_1(sK3) )
    | spl4_1 ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f60,f57,f54])).

fof(f52,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f29,f47])).

fof(f47,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f24,f46])).

fof(f46,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f24,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:29:45 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.49  % (27949)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (27938)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (27941)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (27946)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (27934)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (27941)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f62,f75,f77,f80,f84,f89,f91,f100,f103,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl4_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    $false | spl4_9),
% 0.21/0.50    inference(resolution,[],[f99,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v5_relat_1(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f32,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~v5_relat_1(sK3,sK2) | spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl4_9 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~spl4_4 | spl4_5 | spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f87,f69,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl4_5 <=> ! [X0] : ~v4_relat_1(sK3,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl4_8 <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_8),
% 0.21/0.50    inference(resolution,[],[f88,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~spl4_4 | ~spl4_9 | spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f96,f82,f98,f66])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl4_7 <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ~v5_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | spl4_7),
% 0.21/0.50    inference(resolution,[],[f83,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v5_relat_1(k7_relat_1(X2,X0),X1) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~spl4_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    $false | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f74,f45])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X1] : (~v5_relat_1(sK3,X1)) ) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl4_6 <=> ! [X1] : ~v5_relat_1(sK3,X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ~spl4_8 | ~spl4_1 | spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f85,f60,f54,f87])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl4_1 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl4_3 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_3),
% 0.21/0.50    inference(resolution,[],[f61,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~spl4_7 | ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f57,f54,f82])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl4_2 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_2),
% 0.21/0.50    inference(resolution,[],[f58,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl4_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    $false | ~spl4_5),
% 0.21/0.50    inference(resolution,[],[f70,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v4_relat_1(sK3,sK0)),
% 0.21/0.50    inference(resolution,[],[f31,f23])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    $false | spl4_4),
% 0.21/0.50    inference(resolution,[],[f67,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f30,f23])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl4_4 | spl4_6 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f54,f73,f66])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X1] : (~v5_relat_1(sK3,X1) | ~v1_relat_1(sK3)) ) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f55,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f60,f57,f54])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.21/0.50    inference(resolution,[],[f29,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(backward_demodulation,[],[f24,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.21/0.50    inference(resolution,[],[f38,f23])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27941)------------------------------
% 0.21/0.50  % (27941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27941)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27941)Memory used [KB]: 10618
% 0.21/0.50  % (27941)Time elapsed: 0.096 s
% 0.21/0.50  % (27941)------------------------------
% 0.21/0.50  % (27941)------------------------------
% 0.21/0.50  % (27928)Success in time 0.145 s
%------------------------------------------------------------------------------
