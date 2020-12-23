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
% DateTime   : Thu Dec  3 12:51:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 129 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 323 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f58,f74,f112])).

fof(f112,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f85,f89,f102,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f102,plain,
    ( ~ r2_hidden(sK5(sK1,sK0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(superposition,[],[f89,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f89,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK1,sK0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f85,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,
    ( r2_hidden(sK5(sK1,sK0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f83,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl7_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,
    ( r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f14,f75,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f39,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f74,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f48,f52,f38,f29])).

fof(f38,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f52,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k4_xboole_0(X0,k1_relat_1(sK1)))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f48,f30])).

fof(f48,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0))),sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f14,f45,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( r2_hidden(sK3(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f43,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f43,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f58,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f13,f41,f37])).

fof(f13,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f12,f41,f37])).

fof(f12,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (29327)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (29352)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (29328)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (29332)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f44,f58,f74,f112])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ~spl7_1 | ~spl7_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    $false | (~spl7_1 | ~spl7_2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f85,f89,f102,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~r2_hidden(sK5(sK1,sK0),k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.52    inference(superposition,[],[f89,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK5(sK1,sK0),k4_xboole_0(X0,k1_xboole_0))) ) | (~spl7_1 | ~spl7_2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f85,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1,sK0),k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.22/0.52    inference(forward_demodulation,[],[f83,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl7_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl7_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f14,f75,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1) | ~spl7_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f39,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    spl7_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl7_1 | spl7_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    $false | (spl7_1 | spl7_2)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f48,f52,f38,f29])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl7_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f37])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK0,k4_xboole_0(X0,k1_relat_1(sK1)))) ) | spl7_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f48,f30])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    r2_hidden(sK0,k1_relat_1(sK1)) | spl7_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f46,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK0,sK3(k11_relat_1(sK1,sK0))),sK1) | spl7_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f14,f45,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    r2_hidden(sK3(k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | spl7_2),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f43,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f41])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~spl7_1 | spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f13,f41,f37])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    spl7_1 | ~spl7_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f12,f41,f37])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (29327)------------------------------
% 0.22/0.52  % (29327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29327)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (29327)Memory used [KB]: 6268
% 0.22/0.52  % (29327)Time elapsed: 0.095 s
% 0.22/0.52  % (29327)------------------------------
% 0.22/0.52  % (29327)------------------------------
% 0.22/0.52  % (29320)Success in time 0.154 s
%------------------------------------------------------------------------------
