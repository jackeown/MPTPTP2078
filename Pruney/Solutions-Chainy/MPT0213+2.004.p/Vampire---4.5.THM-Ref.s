%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  66 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 145 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f69,f93])).

fof(f93,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f91,f90])).

fof(f90,plain,
    ( ! [X0] : ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f81,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f81,plain,
    ( ! [X0] : ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f45,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f91,plain,
    ( ! [X2] : r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f86,f90])).

fof(f86,plain,
    ( ! [X2] :
        ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X2)
        | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f67,f66])).

fof(f66,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f60,f25])).

fof(f60,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f49,f36])).

fof(f49,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( ! [X1] : r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f62,f66])).

fof(f62,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X1)
        | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f35])).

fof(f50,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f47,f43])).

fof(f41,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X3] :
      ( k1_xboole_0 != X3
      | r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0)
      | r2_hidden(sK0(k1_xboole_0,X3),X3) ) ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f18,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f16])).

fof(f16,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4672)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.47  % (4672)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (4689)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f50,f69,f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    $false | ~spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f91,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X0)) ) | ~spl4_1),
% 0.20/0.47    inference(forward_demodulation,[],[f81,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | ~spl4_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f45,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl4_1 <=> r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    ( ! [X2] : (r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X2))) ) | ~spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f86,f90])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    ( ! [X2] : (r2_hidden(sK0(k1_xboole_0,k1_xboole_0),X2) | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X2))) ) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f45,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~spl4_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    $false | ~spl4_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f67,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0)) ) | ~spl4_2),
% 0.20/0.47    inference(forward_demodulation,[],[f60,f25])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | ~spl4_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f49,f36])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl4_2 <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X1] : (r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))) ) | ~spl4_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f62,f66])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X1] : (r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X1) | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))) ) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f49,f35])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl4_1 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f47,f43])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.47    inference(equality_resolution,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X3] : (k1_xboole_0 != X3 | r2_hidden(sK2(k1_xboole_0,X3),k1_xboole_0) | r2_hidden(sK0(k1_xboole_0,X3),X3)) )),
% 0.20/0.47    inference(superposition,[],[f18,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,negated_conjecture,(
% 0.20/0.47    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.47    inference(negated_conjecture,[],[f15])).
% 0.20/0.47  fof(f15,conjecture,(
% 0.20/0.47    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4672)------------------------------
% 0.20/0.47  % (4672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4672)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4672)Memory used [KB]: 10746
% 0.20/0.47  % (4672)Time elapsed: 0.054 s
% 0.20/0.47  % (4672)------------------------------
% 0.20/0.47  % (4672)------------------------------
% 0.20/0.47  % (4656)Success in time 0.116 s
%------------------------------------------------------------------------------
