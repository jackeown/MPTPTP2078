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
% DateTime   : Thu Dec  3 12:38:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 120 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 276 expanded)
%              Number of equality atoms :   32 ( 155 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f307,f439])).

fof(f439,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f437,f344])).

fof(f344,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f20,f312,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f312,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_1 ),
    inference(superposition,[],[f143,f134])).

fof(f134,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f143,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f24,f19])).

fof(f19,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f437,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f431,f134])).

fof(f431,plain,(
    r1_tarski(k1_tarski(sK0),sK2) ),
    inference(superposition,[],[f100,f406])).

fof(f406,plain,(
    sK0 = sK3(sK2) ),
    inference(unit_resulting_resolution,[],[f149,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f149,plain,(
    r2_hidden(sK3(sK2),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f143,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f48,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    r1_tarski(k1_tarski(sK3(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f307,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f303,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_2
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f303,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f74,f288])).

fof(f288,plain,(
    sK0 = sK3(sK1) ),
    inference(unit_resulting_resolution,[],[f123,f38])).

fof(f123,plain,(
    r2_hidden(sK3(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f45,f51,f32])).

fof(f51,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f25,f19])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f45,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f21,f23])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f45,f26])).

fof(f140,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f126,f136,f132])).

fof(f126,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f51,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (6130)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (6112)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (6123)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (6114)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (6112)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (6108)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f446,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f140,f307,f439])).
% 0.20/0.57  fof(f439,plain,(
% 0.20/0.57    ~spl6_1),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f438])).
% 0.20/0.57  fof(f438,plain,(
% 0.20/0.57    $false | ~spl6_1),
% 0.20/0.57    inference(subsumption_resolution,[],[f437,f344])).
% 0.20/0.57  fof(f344,plain,(
% 0.20/0.57    ~r1_tarski(sK1,sK2) | ~spl6_1),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f20,f312,f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f312,plain,(
% 0.20/0.57    r1_tarski(sK2,sK1) | ~spl6_1),
% 0.20/0.57    inference(superposition,[],[f143,f134])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    sK1 = k1_tarski(sK0) | ~spl6_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f132])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    spl6_1 <=> sK1 = k1_tarski(sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.57  fof(f143,plain,(
% 0.20/0.57    r1_tarski(sK2,k1_tarski(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f41,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k1_tarski(sK0))) )),
% 0.20/0.57    inference(superposition,[],[f24,f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.57    inference(negated_conjecture,[],[f13])).
% 0.20/0.57  fof(f13,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.57    inference(equality_resolution,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    sK1 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f437,plain,(
% 0.20/0.57    r1_tarski(sK1,sK2) | ~spl6_1),
% 0.20/0.57    inference(forward_demodulation,[],[f431,f134])).
% 0.20/0.57  fof(f431,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK0),sK2)),
% 0.20/0.57    inference(superposition,[],[f100,f406])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    sK0 = sK3(sK2)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f149,f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k1_tarski(X0))) )),
% 0.20/0.57    inference(equality_resolution,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    r2_hidden(sK3(sK2),k1_tarski(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f143,f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    r2_hidden(sK3(sK2),sK2)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f22,f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    k1_xboole_0 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f100,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK3(sK2)),sK2)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.57  fof(f307,plain,(
% 0.20/0.57    spl6_2),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    $false | spl6_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f303,f138])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    ~r1_tarski(k1_tarski(sK0),sK1) | spl6_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f136])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    spl6_2 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.57  fof(f303,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK0),sK1)),
% 0.20/0.57    inference(superposition,[],[f74,f288])).
% 0.20/0.57  fof(f288,plain,(
% 0.20/0.57    sK0 = sK3(sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f123,f38])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    r2_hidden(sK3(sK1),k1_tarski(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f45,f51,f32])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    r1_tarski(sK1,k1_tarski(sK0))),
% 0.20/0.57    inference(superposition,[],[f25,f19])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    r2_hidden(sK3(sK1),sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f21,f23])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f45,f26])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    spl6_1 | ~spl6_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f126,f136,f132])).
% 0.20/0.57  fof(f126,plain,(
% 0.20/0.57    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 0.20/0.57    inference(resolution,[],[f51,f37])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (6112)------------------------------
% 0.20/0.57  % (6112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6112)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (6112)Memory used [KB]: 10874
% 0.20/0.57  % (6112)Time elapsed: 0.123 s
% 0.20/0.57  % (6112)------------------------------
% 0.20/0.57  % (6112)------------------------------
% 0.20/0.58  % (6109)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.58  % (6115)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.58  % (6102)Success in time 0.218 s
%------------------------------------------------------------------------------
