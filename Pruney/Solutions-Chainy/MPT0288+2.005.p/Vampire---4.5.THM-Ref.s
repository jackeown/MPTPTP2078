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
% DateTime   : Thu Dec  3 12:41:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 154 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f47,f173,f326,f371,f407,f485])).

fof(f485,plain,
    ( spl3_1
    | ~ spl3_47 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl3_1
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f481,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f481,plain,
    ( r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | ~ spl3_47 ),
    inference(resolution,[],[f406,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f406,plain,
    ( r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl3_47
  <=> r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f407,plain,
    ( spl3_47
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f402,f368,f404])).

fof(f368,plain,
    ( spl3_45
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f402,plain,
    ( r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl3_45 ),
    inference(resolution,[],[f370,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f370,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f368])).

fof(f371,plain,
    ( spl3_45
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f364,f323,f368])).

fof(f323,plain,
    ( spl3_37
  <=> r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f364,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl3_37 ),
    inference(resolution,[],[f325,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f325,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f323])).

fof(f326,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f315,f170,f45,f323])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f170,plain,
    ( spl3_20
  <=> k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f315,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f46,f172])).

fof(f172,plain,
    ( k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1))))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f46,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f173,plain,
    ( spl3_20
    | spl3_1 ),
    inference(avatar_split_clause,[],[f166,f25,f170])).

fof(f166,plain,
    ( k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1))))
    | spl3_1 ),
    inference(resolution,[],[f81,f27])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | k1_tarski(sK2(X0,X1)) = k3_xboole_0(X0,k1_tarski(sK2(X0,X1))) ) ),
    inference(forward_demodulation,[],[f80,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK2(X0,X1)) = k3_xboole_0(k1_tarski(sK2(X0,X1)),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f30,f45])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

% (3347)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.43  % (3339)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.43  % (3345)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (3338)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (3343)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (3340)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (3341)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  % (3338)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f495,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f28,f33,f47,f173,f326,f371,f407,f485])).
% 0.21/0.45  fof(f485,plain,(
% 0.21/0.45    spl3_1 | ~spl3_47),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f484])).
% 0.21/0.45  fof(f484,plain,(
% 0.21/0.45    $false | (spl3_1 | ~spl3_47)),
% 0.21/0.45    inference(subsumption_resolution,[],[f481,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    spl3_1 <=> r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f481,plain,(
% 0.21/0.45    r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) | ~spl3_47),
% 0.21/0.45    inference(resolution,[],[f406,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.45  fof(f406,plain,(
% 0.21/0.45    r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | ~spl3_47),
% 0.21/0.45    inference(avatar_component_clause,[],[f404])).
% 0.21/0.45  fof(f404,plain,(
% 0.21/0.45    spl3_47 <=> r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.45  fof(f407,plain,(
% 0.21/0.45    spl3_47 | ~spl3_45),
% 0.21/0.45    inference(avatar_split_clause,[],[f402,f368,f404])).
% 0.21/0.45  fof(f368,plain,(
% 0.21/0.45    spl3_45 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.45  fof(f402,plain,(
% 0.21/0.45    r1_tarski(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | ~spl3_45),
% 0.21/0.45    inference(resolution,[],[f370,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.45  fof(f370,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) | ~spl3_45),
% 0.21/0.45    inference(avatar_component_clause,[],[f368])).
% 0.21/0.45  fof(f371,plain,(
% 0.21/0.45    spl3_45 | ~spl3_37),
% 0.21/0.45    inference(avatar_split_clause,[],[f364,f323,f368])).
% 0.21/0.45  fof(f323,plain,(
% 0.21/0.45    spl3_37 <=> r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.45  fof(f364,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK1) | ~spl3_37),
% 0.21/0.45    inference(resolution,[],[f325,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.45  fof(f325,plain,(
% 0.21/0.45    r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1) | ~spl3_37),
% 0.21/0.45    inference(avatar_component_clause,[],[f323])).
% 0.21/0.45  fof(f326,plain,(
% 0.21/0.45    spl3_37 | ~spl3_4 | ~spl3_20),
% 0.21/0.45    inference(avatar_split_clause,[],[f315,f170,f45,f323])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_4 <=> ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f170,plain,(
% 0.21/0.45    spl3_20 <=> k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.45  fof(f315,plain,(
% 0.21/0.45    r1_tarski(k1_tarski(sK2(sK0,k3_tarski(sK1))),sK1) | (~spl3_4 | ~spl3_20)),
% 0.21/0.45    inference(superposition,[],[f46,f172])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1)))) | ~spl3_20),
% 0.21/0.45    inference(avatar_component_clause,[],[f170])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    spl3_20 | spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f166,f25,f170])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    k1_tarski(sK2(sK0,k3_tarski(sK1))) = k3_xboole_0(sK0,k1_tarski(sK2(sK0,k3_tarski(sK1)))) | spl3_1),
% 0.21/0.45    inference(resolution,[],[f81,f27])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | k1_tarski(sK2(X0,X1)) = k3_xboole_0(X0,k1_tarski(sK2(X0,X1)))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f80,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_tarski(sK2(X0,X1)) = k3_xboole_0(k1_tarski(sK2(X0,X1)),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.45    inference(resolution,[],[f36,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.45    inference(resolution,[],[f18,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_4 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f30,f45])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) ) | ~spl3_2),
% 0.21/0.45    inference(resolution,[],[f23,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f30])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  % (3347)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (3338)------------------------------
% 0.21/0.45  % (3338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (3338)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (3338)Memory used [KB]: 10874
% 0.21/0.45  % (3338)Time elapsed: 0.037 s
% 0.21/0.45  % (3338)------------------------------
% 0.21/0.45  % (3338)------------------------------
% 0.21/0.45  % (3344)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (3342)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (3346)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (3336)Success in time 0.093 s
%------------------------------------------------------------------------------
