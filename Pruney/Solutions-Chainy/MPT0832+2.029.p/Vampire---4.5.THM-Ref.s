%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 128 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 276 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f58,f75,f80,f105,f130,f139,f223])).

fof(f223,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(resolution,[],[f221,f52])).

fof(f52,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f221,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_7 ),
    inference(resolution,[],[f64,f110])).

fof(f110,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | spl4_7 ),
    inference(backward_demodulation,[],[f98,f81])).

fof(f81,plain,(
    ! [X0] : k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_7
  <=> v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
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

fof(f139,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | spl4_9 ),
    inference(avatar_split_clause,[],[f136,f103,f78,f51])).

fof(f78,plain,
    ( spl4_4
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f103,plain,
    ( spl4_9
  <=> r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f136,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | spl4_9 ),
    inference(resolution,[],[f126,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl4_9 ),
    inference(resolution,[],[f108,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2)
    | spl4_9 ),
    inference(backward_demodulation,[],[f104,f81])).

fof(f104,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f130,plain,
    ( ~ spl4_1
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl4_1
    | spl4_8 ),
    inference(resolution,[],[f127,f52])).

fof(f127,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_8 ),
    inference(resolution,[],[f109,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f109,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1)
    | spl4_8 ),
    inference(backward_demodulation,[],[f101,f81])).

fof(f101,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_8
  <=> r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f105,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f91,f103,f100,f97])).

fof(f91,plain,
    ( ~ r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)
    | ~ r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)
    | ~ v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ~ m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f16])).

% (18429)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f80,plain,
    ( ~ spl4_1
    | spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f76,f72,f78,f51])).

fof(f72,plain,
    ( spl4_3
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f75,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f70,f51,f72])).

fof(f70,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f38,f65])).

fof(f65,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f55,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f54,f51])).

fof(f48,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f32,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (18423)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (18414)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (18420)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (18418)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (18433)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (18419)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (18415)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (18417)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (18416)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (18434)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (18435)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (18426)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (18425)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (18424)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (18427)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (18428)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (18424)Refutation not found, incomplete strategy% (18424)------------------------------
% 0.22/0.52  % (18424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18424)Memory used [KB]: 10618
% 0.22/0.52  % (18424)Time elapsed: 0.105 s
% 0.22/0.52  % (18424)------------------------------
% 0.22/0.52  % (18424)------------------------------
% 0.22/0.52  % (18426)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f56,f58,f75,f80,f105,f130,f139,f223])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ~spl4_1 | spl4_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f222])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    $false | (~spl4_1 | spl4_7)),
% 0.22/0.52    inference(resolution,[],[f221,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl4_1 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | spl4_7),
% 0.22/0.52    inference(resolution,[],[f64,f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ~v1_relat_1(k8_relat_1(sK1,sK3)) | spl4_7),
% 0.22/0.52    inference(backward_demodulation,[],[f98,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relset_1(sK2,sK0,X0,sK3) = k8_relat_1(X0,sK3)) )),
% 0.22/0.52    inference(resolution,[],[f44,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => m1_subset_1(k6_relset_1(X2,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ~v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)) | spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl4_7 <=> v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(resolution,[],[f49,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f32,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ~spl4_1 | ~spl4_4 | spl4_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f136,f103,f78,f51])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl4_4 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl4_9 <=> r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | spl4_9),
% 0.22/0.52    inference(resolution,[],[f126,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_wellord1)).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),X0) | ~r1_tarski(X0,sK2)) ) | spl4_9),
% 0.22/0.52    inference(resolution,[],[f108,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k8_relat_1(sK1,sK3)),sK2) | spl4_9),
% 0.22/0.52    inference(backward_demodulation,[],[f104,f81])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) | spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f103])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~spl4_1 | spl4_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    $false | (~spl4_1 | spl4_8)),
% 0.22/0.52    inference(resolution,[],[f127,f52])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | spl4_8),
% 0.22/0.52    inference(resolution,[],[f109,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(k8_relat_1(sK1,sK3)),sK1) | spl4_8),
% 0.22/0.52    inference(backward_demodulation,[],[f101,f81])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) | spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl4_8 <=> r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ~spl4_7 | ~spl4_8 | ~spl4_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f91,f103,f100,f97])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK2) | ~r1_tarski(k2_relat_1(k6_relset_1(sK2,sK0,sK1,sK3)),sK1) | ~v1_relat_1(k6_relset_1(sK2,sK0,sK1,sK3))),
% 0.22/0.52    inference(resolution,[],[f41,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ~m1_subset_1(k6_relset_1(sK2,sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % (18429)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~spl4_1 | spl4_4 | ~spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f76,f72,f78,f51])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl4_3 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~spl4_3),
% 0.22/0.52    inference(superposition,[],[f36,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    sK3 = k7_relat_1(sK3,sK2) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl4_3 | ~spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f70,f51,f72])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.52    inference(resolution,[],[f38,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    v4_relat_1(sK3,sK2)),
% 0.22/0.52    inference(resolution,[],[f42,f30])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    $false | spl4_2),
% 0.22/0.52    inference(resolution,[],[f55,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f54,f51])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f32,f30])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (18426)------------------------------
% 0.22/0.52  % (18426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18426)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (18426)Memory used [KB]: 10746
% 0.22/0.52  % (18426)Time elapsed: 0.109 s
% 0.22/0.52  % (18426)------------------------------
% 0.22/0.52  % (18426)------------------------------
% 0.22/0.52  % (18437)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (18432)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (18420)Refutation not found, incomplete strategy% (18420)------------------------------
% 0.22/0.52  % (18420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18420)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18420)Memory used [KB]: 10618
% 0.22/0.52  % (18420)Time elapsed: 0.106 s
% 0.22/0.52  % (18420)------------------------------
% 0.22/0.52  % (18420)------------------------------
% 0.22/0.52  % (18431)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (18422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.53  % (18422)Refutation not found, incomplete strategy% (18422)------------------------------
% 0.22/0.53  % (18422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18422)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18422)Memory used [KB]: 10490
% 0.22/0.53  % (18422)Time elapsed: 0.097 s
% 0.22/0.53  % (18422)------------------------------
% 0.22/0.53  % (18422)------------------------------
% 0.22/0.53  % (18421)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (18436)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.54  % (18413)Success in time 0.183 s
%------------------------------------------------------------------------------
