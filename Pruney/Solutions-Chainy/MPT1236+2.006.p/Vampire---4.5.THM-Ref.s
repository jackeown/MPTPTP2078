%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 104 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    6
%              Number of atoms          :  167 ( 250 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f48,f52,f58,f64,f70,f77,f90,f93])).

fof(f93,plain,
    ( ~ spl1_7
    | spl1_10
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl1_7
    | spl1_10
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f91,f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl1_10
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f91,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_13 ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f89,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl1_13
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f90,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f85,f74,f46,f29,f87])).

fof(f29,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f74,plain,
    ( spl1_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f85,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f31,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f79,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(resolution,[],[f47,f76])).

fof(f76,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k1_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f77,plain,
    ( spl1_11
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f72,f61,f55,f42,f74])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] :
        ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f55,plain,
    ( spl1_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f61,plain,
    ( spl1_9
  <=> k1_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_5
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f57,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(superposition,[],[f43,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f43,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f70,plain,
    ( ~ spl1_10
    | spl1_1
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f61,f24,f67])).

fof(f24,plain,
    ( spl1_1
  <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f65,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | spl1_1
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f26,f63])).

fof(f26,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f64,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f59,f55,f38,f61])).

fof(f38,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = k1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f59,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(resolution,[],[f39,f57])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k1_xboole_0 = k1_struct_0(X0) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f58,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f53,f34,f29,f55])).

fof(f34,plain,
    ( spl1_3
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f53,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_struct_0)).

fof(f40,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f17,f24])).

fof(f17,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (29949)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.44  % (29944)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (29949)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f48,f52,f58,f64,f70,f77,f90,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ~spl1_7 | spl1_10 | ~spl1_13),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    $false | (~spl1_7 | spl1_10 | ~spl1_13)),
% 0.21/0.44    inference(subsumption_resolution,[],[f91,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | spl1_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl1_10 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | (~spl1_7 | ~spl1_13)),
% 0.21/0.44    inference(resolution,[],[f89,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl1_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl1_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl1_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl1_13 <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl1_13 | ~spl1_2 | ~spl1_6 | ~spl1_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f85,f74,f46,f29,f87])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl1_6 <=> ! [X1,X0] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl1_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | (~spl1_2 | ~spl1_6 | ~spl1_11)),
% 0.21/0.44    inference(subsumption_resolution,[],[f79,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f29])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl1_6 | ~spl1_11)),
% 0.21/0.44    inference(resolution,[],[f47,f76])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl1_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f46])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl1_11 | ~spl1_5 | ~spl1_8 | ~spl1_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f72,f61,f55,f42,f74])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl1_5 <=> ! [X0] : (m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl1_8 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl1_9 <=> k1_xboole_0 = k1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl1_5 | ~spl1_8 | ~spl1_9)),
% 0.21/0.44    inference(subsumption_resolution,[],[f71,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl1_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | (~spl1_5 | ~spl1_9)),
% 0.21/0.44    inference(superposition,[],[f43,f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    k1_xboole_0 = k1_struct_0(sK0) | ~spl1_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) ) | ~spl1_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ~spl1_10 | spl1_1 | ~spl1_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f65,f61,f24,f67])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    spl1_1 <=> k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | (spl1_1 | ~spl1_9)),
% 0.21/0.44    inference(backward_demodulation,[],[f26,f63])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) | spl1_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f24])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl1_9 | ~spl1_4 | ~spl1_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f59,f55,f38,f61])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl1_4 <=> ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    k1_xboole_0 = k1_struct_0(sK0) | (~spl1_4 | ~spl1_8)),
% 0.21/0.44    inference(resolution,[],[f39,f57])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) ) | ~spl1_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl1_8 | ~spl1_2 | ~spl1_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f53,f34,f29,f55])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl1_3 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    l1_struct_0(sK0) | (~spl1_2 | ~spl1_3)),
% 0.21/0.44    inference(resolution,[],[f35,f31])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl1_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl1_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl1_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f46])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl1_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f42])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_struct_0)).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl1_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl1_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f34])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl1_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f29])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ~spl1_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f24])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29949)------------------------------
% 0.21/0.44  % (29949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29949)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29949)Memory used [KB]: 6140
% 0.21/0.44  % (29949)Time elapsed: 0.035 s
% 0.21/0.44  % (29949)------------------------------
% 0.21/0.44  % (29949)------------------------------
% 0.21/0.44  % (29938)Success in time 0.09 s
%------------------------------------------------------------------------------
