%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 132 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f27,f31,f35,f39,f43,f54,f59,f62])).

fof(f62,plain,
    ( spl1_1
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | spl1_1
    | ~ spl1_9 ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,
    ( ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f58,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_9
  <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f59,plain,
    ( spl1_9
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f55,f52,f41,f57])).

fof(f41,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f52,plain,
    ( spl1_8
  <=> ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f55,plain,
    ( ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f53,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f50,f37,f33,f29,f25,f52])).

fof(f25,plain,
    ( spl1_2
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f29,plain,
    ( spl1_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f33,plain,
    ( spl1_4
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f37,plain,
    ( spl1_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f50,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f49,f34])).

fof(f34,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f49,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f48,f30])).

fof(f30,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))))
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f38,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f43,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f39,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f35,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f31,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f23,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
   => ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (3895)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.41  % (3896)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.41  % (3897)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.42  % (3895)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f23,f27,f31,f35,f39,f43,f54,f59,f62])).
% 0.19/0.42  fof(f62,plain,(
% 0.19/0.42    spl1_1 | ~spl1_9),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f60])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    $false | (spl1_1 | ~spl1_9)),
% 0.19/0.42    inference(resolution,[],[f58,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl1_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    spl1_1 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl1_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f57])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    spl1_9 <=> ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    spl1_9 | ~spl1_6 | ~spl1_8),
% 0.19/0.42    inference(avatar_split_clause,[],[f55,f52,f41,f57])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    spl1_6 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    spl1_8 <=> ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | (~spl1_6 | ~spl1_8)),
% 0.19/0.42    inference(resolution,[],[f53,f42])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl1_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f41])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) ) | ~spl1_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f52])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    spl1_8 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f50,f37,f33,f29,f25,f52])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    spl1_2 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    spl1_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    spl1_4 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    spl1_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.19/0.42    inference(forward_demodulation,[],[f49,f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f33])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X0))) ) | (~spl1_2 | ~spl1_3 | ~spl1_5)),
% 0.19/0.42    inference(forward_demodulation,[],[f48,f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f29])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0))))) ) | (~spl1_2 | ~spl1_5)),
% 0.19/0.42    inference(resolution,[],[f38,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f25])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl1_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f37])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    spl1_6),
% 0.19/0.42    inference(avatar_split_clause,[],[f18,f41])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    spl1_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f16,f37])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    spl1_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f14,f33])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    spl1_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f15,f29])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    spl1_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f13,f25])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ~spl1_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f12,f20])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0] : ~m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0] : ~m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,negated_conjecture,(
% 0.19/0.42    ~! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.42    inference(negated_conjecture,[],[f5])).
% 0.19/0.42  fof(f5,conjecture,(
% 0.19/0.42    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (3895)------------------------------
% 0.19/0.42  % (3895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (3895)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (3895)Memory used [KB]: 10490
% 0.19/0.42  % (3895)Time elapsed: 0.005 s
% 0.19/0.42  % (3895)------------------------------
% 0.19/0.42  % (3895)------------------------------
% 0.19/0.42  % (3888)Success in time 0.063 s
%------------------------------------------------------------------------------
