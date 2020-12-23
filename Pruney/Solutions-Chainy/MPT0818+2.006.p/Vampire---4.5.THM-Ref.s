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
% DateTime   : Thu Dec  3 12:56:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 188 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f46,f51,f62])).

fof(f62,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(global_subsumption,[],[f52,f38,f60])).

fof(f60,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f26,f45])).

fof(f45,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_3
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f38,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(global_subsumption,[],[f22,f47])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & r1_tarski(k2_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & r1_tarski(k2_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & r1_tarski(k2_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      & r1_tarski(k2_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_tarski(k2_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f22,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f34,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f41,f43,f36])).

fof(f41,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

% (3779)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f39,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f36,f32])).

fof(f30,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (3784)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.41  % (3776)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.41  % (3784)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f39,f46,f51,f62])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    ~spl4_2 | ~spl4_3),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f61])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    $false | (~spl4_2 | ~spl4_3)),
% 0.20/0.41    inference(global_subsumption,[],[f52,f38,f60])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~spl4_3),
% 0.20/0.41    inference(superposition,[],[f26,f45])).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    sK3 = k7_relat_1(sK3,sK2) | ~spl4_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    spl4_3 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    v1_relat_1(sK3) | ~spl4_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    spl4_2 <=> v1_relat_1(sK3)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.20/0.41    inference(global_subsumption,[],[f22,f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    ~r1_tarski(k2_relat_1(sK3),sK1) | ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.20/0.41    inference(resolution,[],[f28,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & r1_tarski(k2_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.41    inference(flattening,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & r1_tarski(k2_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl4_1),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f50])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    $false | spl4_1),
% 0.20/0.41    inference(resolution,[],[f34,f25])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl4_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl4_1 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    ~spl4_2 | spl4_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f41,f43,f36])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    sK3 = k7_relat_1(sK3,sK2) | ~v1_relat_1(sK3)),
% 0.20/0.41    inference(resolution,[],[f27,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    v4_relat_1(sK3,sK2)),
% 0.20/0.41    inference(resolution,[],[f29,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f20])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  % (3779)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(flattening,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ~spl4_1 | spl4_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f30,f36,f32])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.20/0.41    inference(resolution,[],[f24,f21])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (3784)------------------------------
% 0.20/0.41  % (3784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (3784)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (3784)Memory used [KB]: 10618
% 0.20/0.41  % (3784)Time elapsed: 0.005 s
% 0.20/0.41  % (3784)------------------------------
% 0.20/0.41  % (3784)------------------------------
% 0.20/0.41  % (3772)Success in time 0.059 s
%------------------------------------------------------------------------------
