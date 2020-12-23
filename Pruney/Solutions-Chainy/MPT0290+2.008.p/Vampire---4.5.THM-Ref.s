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
% DateTime   : Thu Dec  3 12:41:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 141 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f87,f124])).

fof(f124,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f102,f91,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f91,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f48,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_2
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),sK1)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f92,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f92,plain,
    ( ~ r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),k3_tarski(sK1))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f60,f50,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f44,f15])).

fof(f44,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_1
  <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),sK0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f51,f17])).

fof(f51,plain,
    ( ~ r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),k3_tarski(sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f44,f16])).

fof(f49,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f46,f42])).

fof(f40,plain,
    ( ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f14,f24])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f25,plain,(
    ~ r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(definition_unfolding,[],[f13,f24,f24])).

fof(f13,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n025.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:29:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (15599)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (15591)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15606)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (15594)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (15601)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (15596)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f49,f87,f124])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    $false | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f102,f91,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(equality_resolution,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.22/0.55    inference(definition_unfolding,[],[f22,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f48,f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    spl4_2 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),sK1) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f92,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ~r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK1)),k3_tarski(sK1)) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f48,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    spl4_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    $false | spl4_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f60,f50,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(equality_resolution,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.22/0.55    inference(definition_unfolding,[],[f21,f24])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f44,f15])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0)) | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    spl4_1 <=> r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),sK0) | spl4_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f51,f17])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ~r1_tarski(sK2(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_tarski(sK0)),k3_tarski(sK0)) | spl4_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f44,f16])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ~spl4_1 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f40,f46,f42])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k3_tarski(sK0))),
% 0.22/0.55    inference(resolution,[],[f25,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f14,f24])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ~r1_tarski(k3_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k3_tarski(sK0),k4_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 0.22/0.55    inference(definition_unfolding,[],[f13,f24,f24])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.55    inference(negated_conjecture,[],[f6])).
% 0.22/0.55  fof(f6,conjecture,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (15596)------------------------------
% 0.22/0.55  % (15596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15596)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (15596)Memory used [KB]: 6268
% 0.22/0.55  % (15596)Time elapsed: 0.124 s
% 0.22/0.55  % (15596)------------------------------
% 0.22/0.55  % (15596)------------------------------
% 0.22/0.55  % (15588)Success in time 0.176 s
%------------------------------------------------------------------------------
