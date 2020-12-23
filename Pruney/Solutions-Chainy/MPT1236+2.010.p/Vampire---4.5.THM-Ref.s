%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :  102 ( 140 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f42,f48,f54,f60,f66,f72])).

fof(f72,plain,
    ( spl1_6
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl1_6
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f68,f59])).

fof(f59,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_6
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f68,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl1_7 ),
    inference(superposition,[],[f19,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_7
  <=> k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f66,plain,
    ( spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f61,f51,f63])).

fof(f51,plain,
    ( spl1_5
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f61,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_5 ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f60,plain,
    ( ~ spl1_6
    | spl1_1
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f55,f39,f27,f57])).

fof(f27,plain,
    ( spl1_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f39,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f55,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f29,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f29,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f54,plain,
    ( spl1_5
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f49,f46,f51])).

fof(f46,plain,
    ( spl1_4
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_4 ),
    inference(resolution,[],[f47,f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f47,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f48,plain,
    ( spl1_4
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f44,f32,f46])).

fof(f32,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k1_tops_1(sK0,X0),X0) )
    | ~ spl1_2 ),
    inference(resolution,[],[f22,f34])).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f42,plain,
    ( spl1_3
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f37,f32,f39])).

fof(f37,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f20,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f35,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f30,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.42  % (20327)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (20329)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (20322)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (20326)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (20322)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f30,f35,f42,f48,f54,f60,f66,f72])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl1_6 | ~spl1_7),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    $false | (spl1_6 | ~spl1_7)),
% 0.22/0.43    inference(subsumption_resolution,[],[f68,f59])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    spl1_6 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl1_7),
% 0.22/0.43    inference(superposition,[],[f19,f65])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl1_7 <=> k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl1_7 | ~spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f61,f51,f63])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl1_5 <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl1_5),
% 0.22/0.43    inference(resolution,[],[f53,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f51])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ~spl1_6 | spl1_1 | ~spl1_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f55,f39,f27,f57])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    spl1_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl1_3 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl1_1 | ~spl1_3)),
% 0.22/0.43    inference(superposition,[],[f29,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f39])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f27])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl1_5 | ~spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f49,f46,f51])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl1_4 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl1_4),
% 0.22/0.43    inference(resolution,[],[f47,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f46])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl1_4 | ~spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f44,f32,f46])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    spl1_2 <=> l1_pre_topc(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) ) | ~spl1_2),
% 0.22/0.43    inference(resolution,[],[f22,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    l1_pre_topc(sK0) | ~spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f32])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl1_3 | ~spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f37,f32,f39])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_2),
% 0.22/0.43    inference(resolution,[],[f36,f34])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.22/0.43    inference(resolution,[],[f20,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f32])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    l1_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ~spl1_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f27])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (20322)------------------------------
% 0.22/0.43  % (20322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (20322)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (20322)Memory used [KB]: 10618
% 0.22/0.43  % (20322)Time elapsed: 0.006 s
% 0.22/0.43  % (20322)------------------------------
% 0.22/0.43  % (20322)------------------------------
% 0.22/0.44  % (20320)Success in time 0.075 s
%------------------------------------------------------------------------------
