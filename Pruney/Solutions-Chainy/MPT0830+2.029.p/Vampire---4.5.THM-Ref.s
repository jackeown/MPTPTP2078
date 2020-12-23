%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 121 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 285 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f52,f78,f84,f96,f99,f110,f140,f150,f168])).

fof(f168,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f149,f59])).

fof(f59,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f149,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_15
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f150,plain,
    ( ~ spl4_15
    | ~ spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f145,f138,f45,f148])).

fof(f45,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f138,plain,
    ( spl4_13
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f145,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK2)
    | spl4_13 ),
    inference(resolution,[],[f139,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f139,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( ~ spl4_1
    | ~ spl4_13
    | spl4_4 ),
    inference(avatar_split_clause,[],[f134,f73,f138,f45])).

fof(f73,plain,
    ( spl4_4
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f134,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(resolution,[],[f112,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl4_4 ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f74,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f110,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl4_6 ),
    inference(resolution,[],[f83,f58])).

fof(f58,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,
    ( ! [X0] : ~ v4_relat_1(sK3,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_6
  <=> ! [X0] : ~ v4_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f99,plain,
    ( ~ spl4_1
    | spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f97,f94,f82,f45])).

fof(f94,plain,
    ( spl4_8
  <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_8 ),
    inference(resolution,[],[f95,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f95,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( ~ spl4_8
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f91,f76,f70,f94])).

fof(f70,plain,
    ( spl4_3
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( spl4_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f91,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v4_relat_1(k7_relat_1(sK3,sK1),sK1)
    | spl4_5 ),
    inference(resolution,[],[f77,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f77,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f84,plain,
    ( ~ spl4_1
    | spl4_6
    | spl4_3 ),
    inference(avatar_split_clause,[],[f79,f70,f82,f45])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_3 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f78,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f68,f76,f73,f70])).

fof(f68,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f35,f63])).

fof(f63,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f27,f62])).

fof(f62,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f42,f26])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f27,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f49,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f43,f48,f45])).

fof(f43,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (1101)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (1101)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1110)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f50,f52,f78,f84,f96,f99,f110,f140,f150,f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl4_15),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    $false | spl4_15),
% 0.21/0.49    inference(resolution,[],[f149,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK2)),
% 0.21/0.49    inference(resolution,[],[f37,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~v5_relat_1(sK3,sK2) | spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl4_15 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ~spl4_15 | ~spl4_1 | spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f145,f138,f45,f148])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_1 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl4_13 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK2) | spl4_13),
% 0.21/0.49    inference(resolution,[],[f139,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),sK2) | spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_13 | spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f134,f73,f138,f45])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl4_4 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | spl4_4),
% 0.21/0.49    inference(resolution,[],[f112,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),X0) | ~r1_tarski(X0,sK2)) ) | spl4_4),
% 0.21/0.49    inference(resolution,[],[f74,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    $false | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f83,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v4_relat_1(sK3,sK0)),
% 0.21/0.49    inference(resolution,[],[f36,f26])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0)) ) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_6 <=> ! [X0] : ~v4_relat_1(sK3,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~spl4_1 | spl4_6 | spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f97,f94,f82,f45])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl4_8 <=> v4_relat_1(k7_relat_1(sK3,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_8),
% 0.21/0.49    inference(resolution,[],[f95,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~spl4_8 | ~spl4_3 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f76,f70,f94])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl4_3 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v4_relat_1(k7_relat_1(sK3,sK1),sK1) | spl4_5),
% 0.21/0.49    inference(resolution,[],[f77,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl4_1 | spl4_6 | spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f70,f82,f45])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_3),
% 0.21/0.49    inference(resolution,[],[f71,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f68,f76,f73,f70])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.21/0.49    inference(resolution,[],[f35,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(backward_demodulation,[],[f27,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.21/0.49    inference(resolution,[],[f42,f26])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    $false | spl4_2),
% 0.21/0.49    inference(resolution,[],[f49,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f48,f45])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f28,f26])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1101)------------------------------
% 0.21/0.49  % (1101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1101)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1101)Memory used [KB]: 10618
% 0.21/0.49  % (1101)Time elapsed: 0.065 s
% 0.21/0.49  % (1101)------------------------------
% 0.21/0.49  % (1101)------------------------------
% 0.21/0.49  % (1086)Success in time 0.135 s
%------------------------------------------------------------------------------
