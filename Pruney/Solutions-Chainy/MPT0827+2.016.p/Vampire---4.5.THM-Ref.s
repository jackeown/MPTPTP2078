%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 103 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 320 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f49,f58,f62,f80])).

fof(f80,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f78,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f78,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | spl4_2
    | ~ spl4_4 ),
    inference(global_subsumption,[],[f48,f73,f75])).

fof(f75,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f73,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl4_2 ),
    inference(forward_demodulation,[],[f38,f56])).

fof(f56,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f38,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f22])).

fof(f60,plain,
    ( ~ v1_relat_1(k6_relat_1(sK2))
    | spl4_1
    | ~ spl4_4 ),
    inference(global_subsumption,[],[f55,f48,f59])).

fof(f59,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f50,f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_1 ),
    inference(backward_demodulation,[],[f34,f54])).

fof(f54,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f34,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_3
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f49,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f40,f46,f42])).

fof(f40,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f27,f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f39,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f21,f36,f32])).

fof(f21,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (5442)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.42  % (5442)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f39,f49,f58,f62,f80])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl4_2 | ~spl4_4),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    $false | (spl4_2 | ~spl4_4)),
% 0.21/0.42    inference(resolution,[],[f78,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ~v1_relat_1(k6_relat_1(sK2)) | (spl4_2 | ~spl4_4)),
% 0.21/0.43    inference(global_subsumption,[],[f48,f73,f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    r1_tarski(sK2,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2))),
% 0.21/0.43    inference(resolution,[],[f52,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(superposition,[],[f26,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k2_relat_1(sK3)) | spl4_2),
% 0.21/0.43    inference(forward_demodulation,[],[f38,f56])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.43    inference(resolution,[],[f30,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl4_2 <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl4_1 | ~spl4_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    $false | (spl4_1 | ~spl4_4)),
% 0.21/0.43    inference(resolution,[],[f60,f22])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ~v1_relat_1(k6_relat_1(sK2)) | (spl4_1 | ~spl4_4)),
% 0.21/0.43    inference(global_subsumption,[],[f55,f48,f59])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2))),
% 0.21/0.43    inference(resolution,[],[f50,f20])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(superposition,[],[f25,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_1),
% 0.21/0.43    inference(backward_demodulation,[],[f34,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.43    inference(resolution,[],[f29,f19])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl4_1 <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    $false | spl4_3),
% 0.21/0.43    inference(resolution,[],[f44,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl4_3 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ~spl4_3 | spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f40,f46,f42])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.43    inference(resolution,[],[f27,f19])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ~spl4_1 | ~spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f36,f32])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (5442)------------------------------
% 0.21/0.43  % (5442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (5442)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (5442)Memory used [KB]: 10618
% 0.21/0.43  % (5442)Time elapsed: 0.007 s
% 0.21/0.43  % (5442)------------------------------
% 0.21/0.43  % (5442)------------------------------
% 0.21/0.43  % (5440)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (5430)Success in time 0.071 s
%------------------------------------------------------------------------------
