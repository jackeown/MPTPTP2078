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
% DateTime   : Thu Dec  3 12:44:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 145 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 330 expanded)
%              Number of equality atoms :   27 (  71 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f87,f106,f170,f177,f250,f255,f273,f347,f374])).

fof(f374,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f327,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f54,f108])).

fof(f108,plain,
    ( k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f45,f57])).

fof(f57,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f54,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f327,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK0),sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f169,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f169,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_6
  <=> r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f347,plain,
    ( spl3_2
    | ~ spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f93,f80,f247,f56])).

fof(f247,plain,
    ( spl3_8
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f80,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f93,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f40])).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f273,plain,
    ( ~ spl3_2
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl3_2
    | spl3_8 ),
    inference(resolution,[],[f262,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f262,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_2
    | spl3_8 ),
    inference(forward_demodulation,[],[f248,f57])).

fof(f248,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f247])).

fof(f255,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f245,f39])).

fof(f245,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f250,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f211,f103,f247,f243])).

fof(f103,plain,
    ( spl3_5
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f211,plain,
    ( r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f194,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f194,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f105,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f105,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f177,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f86,f21])).

fof(f21,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f86,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f170,plain,
    ( spl3_4
    | spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f151,f56,f167,f84])).

fof(f151,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f150,f108])).

fof(f150,plain,
    ( r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f65,f57])).

fof(f65,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f106,plain,
    ( spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f78,f103,f56])).

fof(f78,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f44,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f18,f22])).

fof(f22,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f18,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f48,f84,f80])).

fof(f48,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f26])).

fof(f59,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f56,f52])).

fof(f43,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f42])).

fof(f42,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f19,f22])).

fof(f19,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (16923)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % (16906)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (16903)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (16913)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (16912)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (16902)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (16926)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (16917)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (16923)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f59,f87,f106,f170,f177,f250,f255,f273,f347,f374])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    spl3_1 | ~spl3_2 | ~spl3_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f372])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    $false | (spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~r1_tarski(k4_xboole_0(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 0.21/0.50    inference(backward_demodulation,[],[f54,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) | ~spl3_2),
% 0.21/0.50    inference(backward_demodulation,[],[f45,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    sK0 = sK1 | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl3_2 <=> sK0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f20,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK0,sK0),sK0) | ~spl3_6),
% 0.21/0.50    inference(resolution,[],[f169,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl3_6 <=> r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    spl3_2 | ~spl3_8 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f93,f80,f247,f56])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    spl3_8 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f88,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f82,f40])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~spl3_2 | spl3_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    $false | (~spl3_2 | spl3_8)),
% 0.21/0.50    inference(resolution,[],[f262,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK0) | (~spl3_2 | spl3_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f248,f57])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK1) | spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f247])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    $false | spl3_7),
% 0.21/0.50    inference(resolution,[],[f245,f39])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK1) | spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f243])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl3_7 <=> r1_tarski(sK1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ~spl3_7 | spl3_8 | ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f211,f103,f247,f243])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl3_5 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~r1_tarski(sK1,sK1) | ~spl3_5),
% 0.21/0.50    inference(superposition,[],[f194,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | ~spl3_5),
% 0.21/0.50    inference(resolution,[],[f105,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~spl3_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f86,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl3_4 | spl3_6 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f151,f56,f167,f84])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    r2_hidden(k4_xboole_0(sK0,sK0),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f150,f108])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.50    inference(forward_demodulation,[],[f65,f57])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f46,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f20,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_2 | spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f103,f56])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK0,sK1),sK1) | sK0 = sK1),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f45])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f18,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl3_3 | spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f84,f80])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f20,f26])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f56,f52])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.21/0.50    inference(inner_rewriting,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f19,f22])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (16923)------------------------------
% 0.21/0.50  % (16923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16923)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (16923)Memory used [KB]: 10746
% 0.21/0.50  % (16923)Time elapsed: 0.101 s
% 0.21/0.50  % (16923)------------------------------
% 0.21/0.50  % (16923)------------------------------
% 0.21/0.50  % (16897)Success in time 0.142 s
%------------------------------------------------------------------------------
