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
% DateTime   : Thu Dec  3 12:29:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 158 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f44,f53,f70,f89,f104,f119])).

fof(f119,plain,
    ( ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f116,f69])).

% (18700)Refutation not found, incomplete strategy% (18700)------------------------------
% (18700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18711)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f69,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_5
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f116,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f103,f16])).

% (18707)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f16,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f103,plain,
    ( sP4(sK2(sK0),sK0,sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_7
  <=> sP4(sK2(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f104,plain,
    ( spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f90,f87,f102])).

fof(f87,plain,
    ( spl7_6
  <=> r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f90,plain,
    ( sP4(sK2(sK0),sK0,sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,
    ( r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f55,f51,f87])).

fof(f51,plain,
    ( spl7_4
  <=> sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f55,plain,
    ( r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f52,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f52,plain,
    ( sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f70,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f54,f51,f68])).

fof(f54,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f52,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,
    ( spl7_4
    | spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f49,f42,f33,f51])).

fof(f33,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f42,plain,
    ( spl7_3
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f49,plain,
    ( sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0)
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f46,f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f46,plain,
    ( sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0)
    | k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(resolution,[],[f45,f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f45,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sP6(X0,k4_xboole_0(sK1,sK0),sK0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f40,f37,f42])).

fof(f37,plain,
    ( spl7_2
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f40,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl7_2 ),
    inference(resolution,[],[f38,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f10,f37])).

fof(f10,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f35,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f11,f33])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (18704)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (18698)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (18698)Refutation not found, incomplete strategy% (18698)------------------------------
% 0.20/0.46  % (18698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (18697)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (18698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18698)Memory used [KB]: 10490
% 0.20/0.47  % (18698)Time elapsed: 0.064 s
% 0.20/0.47  % (18698)------------------------------
% 0.20/0.47  % (18698)------------------------------
% 0.20/0.47  % (18700)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (18697)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f35,f39,f44,f53,f70,f89,f104,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~spl7_5 | ~spl7_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    $false | (~spl7_5 | ~spl7_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f69])).
% 0.20/0.47  % (18700)Refutation not found, incomplete strategy% (18700)------------------------------
% 0.20/0.47  % (18700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18711)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    r2_hidden(sK2(sK0),sK0) | ~spl7_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl7_5 <=> r2_hidden(sK2(sK0),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ~r2_hidden(sK2(sK0),sK0) | ~spl7_7),
% 0.20/0.47    inference(resolution,[],[f103,f16])).
% 0.20/0.47  % (18707)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    sP4(sK2(sK0),sK0,sK1) | ~spl7_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl7_7 <=> sP4(sK2(sK0),sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl7_7 | ~spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f90,f87,f102])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl7_6 <=> r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    sP4(sK2(sK0),sK0,sK1) | ~spl7_6),
% 0.20/0.47    inference(resolution,[],[f88,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP4(X3,X1,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0)) | ~spl7_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl7_6 | ~spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f51,f87])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl7_4 <=> sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r2_hidden(sK2(sK0),k4_xboole_0(sK1,sK0)) | ~spl7_4),
% 0.20/0.47    inference(resolution,[],[f52,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0) | ~spl7_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl7_5 | ~spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f51,f68])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    r2_hidden(sK2(sK0),sK0) | ~spl7_4),
% 0.20/0.47    inference(resolution,[],[f52,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl7_4 | spl7_1 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f42,f33,f51])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl7_1 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl7_3 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0) | (spl7_1 | ~spl7_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f46,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k1_xboole_0 != sK0 | spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    sP6(sK2(sK0),k4_xboole_0(sK1,sK0),sK0) | k1_xboole_0 = sK0 | ~spl7_3),
% 0.20/0.47    inference(resolution,[],[f45,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | sP6(X0,k4_xboole_0(sK1,sK0),sK0)) ) | ~spl7_3),
% 0.20/0.47    inference(superposition,[],[f30,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f42])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | sP6(X3,X1,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl7_3 | ~spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f37,f42])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl7_2 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl7_2),
% 0.20/0.47    inference(resolution,[],[f38,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK0)) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f10,f37])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f11,f33])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (18697)------------------------------
% 0.20/0.47  % (18697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18697)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (18697)Memory used [KB]: 6140
% 0.20/0.47  % (18697)Time elapsed: 0.055 s
% 0.20/0.47  % (18697)------------------------------
% 0.20/0.47  % (18697)------------------------------
% 0.20/0.48  % (18696)Success in time 0.119 s
%------------------------------------------------------------------------------
