%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:01 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 137 expanded)
%              Number of leaves         :   18 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  163 ( 277 expanded)
%              Number of equality atoms :   38 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f122,f563,f582,f2339])).

fof(f2339,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f2336,f579,f55,f50])).

fof(f50,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f579,plain,
    ( spl5_14
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2336,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(superposition,[],[f2299,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2299,plain,
    ( ! [X14] : r1_tarski(sK0,k2_xboole_0(sK1,X14))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f2274])).

fof(f2274,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(sK0,k2_xboole_0(sK1,X14)) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(superposition,[],[f37,f1810])).

fof(f1810,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1792,f1282])).

fof(f1282,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,X2),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f1231,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1231,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,X0),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f444,f57])).

fof(f57,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f444,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(X3,X4)
      | r1_xboole_0(k4_xboole_0(X3,X5),X4) ) ),
    inference(resolution,[],[f432,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f432,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f134,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1792,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f1637,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1637,plain,
    ( ! [X33] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X33)),sK2)
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f1631,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1631,plain,
    ( ! [X33] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X33),sK2)
    | ~ spl5_14 ),
    inference(superposition,[],[f1483,f581])).

fof(f581,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f579])).

fof(f1483,plain,(
    ! [X28,X29,X27] : r1_tarski(k4_xboole_0(X27,X28),k2_xboole_0(X27,X29)) ),
    inference(superposition,[],[f1445,f446])).

fof(f446,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X8) = X8 ),
    inference(resolution,[],[f432,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1445,plain,(
    ! [X24,X23,X22] : r1_tarski(X22,k2_xboole_0(k2_xboole_0(X22,X23),X24)) ),
    inference(trivial_inequality_removal,[],[f1422])).

fof(f1422,plain,(
    ! [X24,X23,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X22,k2_xboole_0(k2_xboole_0(X22,X23),X24)) ) ),
    inference(superposition,[],[f37,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f235,f117])).

fof(f117,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f36,f75])).

fof(f75,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(superposition,[],[f26,f65])).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f235,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f38,f114])).

fof(f114,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f36,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f582,plain,
    ( spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f571,f560,f579])).

fof(f560,plain,
    ( spl5_12
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f571,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f562,f30])).

fof(f562,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f560])).

fof(f563,plain,
    ( spl5_12
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f557,f119,f560])).

fof(f119,plain,
    ( spl5_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f557,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f545])).

fof(f545,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl5_7 ),
    inference(superposition,[],[f167,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f167,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 != k4_xboole_0(X13,k2_xboole_0(X14,X15))
      | r1_tarski(k4_xboole_0(X13,X14),X15) ) ),
    inference(superposition,[],[f37,f38])).

fof(f122,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f113,f60,f119])).

fof(f60,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f113,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f36,f62])).

fof(f62,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (11152)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (11176)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (11168)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (11171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (11179)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (11157)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.59  % (11153)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (11163)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.59  % (11175)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (11156)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (11167)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (11163)Refutation not found, incomplete strategy% (11163)------------------------------
% 0.21/0.60  % (11163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (11163)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (11163)Memory used [KB]: 10618
% 0.21/0.60  % (11163)Time elapsed: 0.166 s
% 0.21/0.60  % (11163)------------------------------
% 0.21/0.60  % (11163)------------------------------
% 0.21/0.60  % (11169)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.61  % (11155)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.61  % (11158)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.86/0.61  % (11177)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.86/0.62  % (11154)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.86/0.62  % (11180)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.86/0.62  % (11159)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.86/0.62  % (11178)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.86/0.62  % (11166)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.86/0.63  % (11169)Refutation not found, incomplete strategy% (11169)------------------------------
% 1.86/0.63  % (11169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.63  % (11169)Termination reason: Refutation not found, incomplete strategy
% 1.86/0.63  
% 1.86/0.63  % (11169)Memory used [KB]: 10618
% 1.86/0.63  % (11169)Time elapsed: 0.179 s
% 1.86/0.63  % (11169)------------------------------
% 1.86/0.63  % (11169)------------------------------
% 1.86/0.63  % (11181)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.86/0.63  % (11161)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.86/0.63  % (11160)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.86/0.64  % (11164)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.12/0.64  % (11173)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.12/0.64  % (11172)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.12/0.64  % (11174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.12/0.64  % (11165)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.12/0.64  % (11174)Refutation not found, incomplete strategy% (11174)------------------------------
% 2.12/0.64  % (11174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (11174)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.64  
% 2.12/0.64  % (11174)Memory used [KB]: 10618
% 2.12/0.64  % (11174)Time elapsed: 0.216 s
% 2.12/0.64  % (11174)------------------------------
% 2.12/0.64  % (11174)------------------------------
% 2.12/0.64  % (11170)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.26/0.66  % (11162)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.26/0.66  % (11162)Refutation not found, incomplete strategy% (11162)------------------------------
% 2.26/0.66  % (11162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (11162)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.66  
% 2.26/0.66  % (11162)Memory used [KB]: 10618
% 2.26/0.66  % (11162)Time elapsed: 0.225 s
% 2.26/0.66  % (11162)------------------------------
% 2.26/0.66  % (11162)------------------------------
% 2.26/0.70  % (11168)Refutation found. Thanks to Tanya!
% 2.26/0.70  % SZS status Theorem for theBenchmark
% 2.68/0.72  % SZS output start Proof for theBenchmark
% 2.68/0.72  fof(f2340,plain,(
% 2.68/0.72    $false),
% 2.68/0.72    inference(avatar_sat_refutation,[],[f53,f58,f63,f122,f563,f582,f2339])).
% 2.68/0.72  fof(f2339,plain,(
% 2.68/0.72    spl5_1 | ~spl5_2 | ~spl5_14),
% 2.68/0.72    inference(avatar_split_clause,[],[f2336,f579,f55,f50])).
% 2.68/0.72  fof(f50,plain,(
% 2.68/0.72    spl5_1 <=> r1_tarski(sK0,sK1)),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.68/0.72  fof(f55,plain,(
% 2.68/0.72    spl5_2 <=> r1_xboole_0(sK0,sK2)),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.68/0.72  fof(f579,plain,(
% 2.68/0.72    spl5_14 <=> sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.68/0.72  fof(f2336,plain,(
% 2.68/0.72    r1_tarski(sK0,sK1) | (~spl5_2 | ~spl5_14)),
% 2.68/0.72    inference(superposition,[],[f2299,f25])).
% 2.68/0.72  fof(f25,plain,(
% 2.68/0.72    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.68/0.72    inference(cnf_transformation,[],[f7])).
% 2.68/0.72  fof(f7,axiom,(
% 2.68/0.72    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.68/0.72  fof(f2299,plain,(
% 2.68/0.72    ( ! [X14] : (r1_tarski(sK0,k2_xboole_0(sK1,X14))) ) | (~spl5_2 | ~spl5_14)),
% 2.68/0.72    inference(trivial_inequality_removal,[],[f2274])).
% 2.68/0.72  fof(f2274,plain,(
% 2.68/0.72    ( ! [X14] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(sK1,X14))) ) | (~spl5_2 | ~spl5_14)),
% 2.68/0.72    inference(superposition,[],[f37,f1810])).
% 2.68/0.72  fof(f1810,plain,(
% 2.68/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | (~spl5_2 | ~spl5_14)),
% 2.68/0.72    inference(forward_demodulation,[],[f1792,f1282])).
% 2.68/0.72  fof(f1282,plain,(
% 2.68/0.72    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,X2),sK2)) ) | ~spl5_2),
% 2.68/0.72    inference(resolution,[],[f1231,f32])).
% 2.68/0.72  fof(f32,plain,(
% 2.68/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.68/0.72    inference(cnf_transformation,[],[f4])).
% 2.68/0.72  fof(f4,axiom,(
% 2.68/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.68/0.72  fof(f1231,plain,(
% 2.68/0.72    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,X0),sK2)) ) | ~spl5_2),
% 2.68/0.72    inference(resolution,[],[f444,f57])).
% 2.68/0.72  fof(f57,plain,(
% 2.68/0.72    r1_xboole_0(sK0,sK2) | ~spl5_2),
% 2.68/0.72    inference(avatar_component_clause,[],[f55])).
% 2.68/0.72  fof(f444,plain,(
% 2.68/0.72    ( ! [X4,X5,X3] : (~r1_xboole_0(X3,X4) | r1_xboole_0(k4_xboole_0(X3,X5),X4)) )),
% 2.68/0.72    inference(resolution,[],[f432,f39])).
% 2.68/0.72  fof(f39,plain,(
% 2.68/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.68/0.72    inference(cnf_transformation,[],[f21])).
% 2.68/0.72  fof(f21,plain,(
% 2.68/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.68/0.72    inference(flattening,[],[f20])).
% 2.68/0.72  fof(f20,plain,(
% 2.68/0.72    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.68/0.72    inference(ennf_transformation,[],[f11])).
% 2.68/0.72  fof(f11,axiom,(
% 2.68/0.72    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.68/0.72  fof(f432,plain,(
% 2.68/0.72    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.68/0.72    inference(duplicate_literal_removal,[],[f417])).
% 2.68/0.72  fof(f417,plain,(
% 2.68/0.72    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.68/0.72    inference(resolution,[],[f134,f35])).
% 2.68/0.72  fof(f35,plain,(
% 2.68/0.72    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.68/0.72    inference(cnf_transformation,[],[f19])).
% 2.68/0.72  fof(f19,plain,(
% 2.68/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.68/0.72    inference(ennf_transformation,[],[f2])).
% 2.68/0.72  fof(f2,axiom,(
% 2.68/0.72    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.68/0.72  fof(f134,plain,(
% 2.68/0.72    ( ! [X2,X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.68/0.72    inference(resolution,[],[f48,f34])).
% 2.68/0.72  fof(f34,plain,(
% 2.68/0.72    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.68/0.72    inference(cnf_transformation,[],[f19])).
% 2.68/0.72  fof(f48,plain,(
% 2.68/0.72    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.68/0.72    inference(equality_resolution,[],[f43])).
% 2.68/0.72  fof(f43,plain,(
% 2.68/0.72    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.68/0.72    inference(cnf_transformation,[],[f3])).
% 2.68/0.72  fof(f3,axiom,(
% 2.68/0.72    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.68/0.72  fof(f1792,plain,(
% 2.68/0.72    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k3_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),sK2)) ) | ~spl5_14),
% 2.68/0.72    inference(resolution,[],[f1637,f29])).
% 2.68/0.72  fof(f29,plain,(
% 2.68/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.68/0.72    inference(cnf_transformation,[],[f17])).
% 2.68/0.72  fof(f17,plain,(
% 2.68/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.68/0.72    inference(ennf_transformation,[],[f8])).
% 2.68/0.72  fof(f8,axiom,(
% 2.68/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.68/0.72  fof(f1637,plain,(
% 2.68/0.72    ( ! [X33] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X33)),sK2)) ) | ~spl5_14),
% 2.68/0.72    inference(forward_demodulation,[],[f1631,f38])).
% 2.68/0.72  fof(f38,plain,(
% 2.68/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.68/0.72    inference(cnf_transformation,[],[f10])).
% 2.68/0.72  fof(f10,axiom,(
% 2.68/0.72    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.68/0.72  fof(f1631,plain,(
% 2.68/0.72    ( ! [X33] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),X33),sK2)) ) | ~spl5_14),
% 2.68/0.72    inference(superposition,[],[f1483,f581])).
% 2.68/0.72  fof(f581,plain,(
% 2.68/0.72    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl5_14),
% 2.68/0.72    inference(avatar_component_clause,[],[f579])).
% 2.68/0.72  fof(f1483,plain,(
% 2.68/0.72    ( ! [X28,X29,X27] : (r1_tarski(k4_xboole_0(X27,X28),k2_xboole_0(X27,X29))) )),
% 2.68/0.72    inference(superposition,[],[f1445,f446])).
% 2.68/0.72  fof(f446,plain,(
% 2.68/0.72    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X8) = X8) )),
% 2.68/0.72    inference(resolution,[],[f432,f30])).
% 2.68/0.72  fof(f30,plain,(
% 2.68/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.68/0.72    inference(cnf_transformation,[],[f18])).
% 2.68/0.72  fof(f18,plain,(
% 2.68/0.72    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.68/0.72    inference(ennf_transformation,[],[f6])).
% 2.68/0.72  fof(f6,axiom,(
% 2.68/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.68/0.72  fof(f1445,plain,(
% 2.68/0.72    ( ! [X24,X23,X22] : (r1_tarski(X22,k2_xboole_0(k2_xboole_0(X22,X23),X24))) )),
% 2.68/0.72    inference(trivial_inequality_removal,[],[f1422])).
% 2.68/0.72  fof(f1422,plain,(
% 2.68/0.72    ( ! [X24,X23,X22] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X22,k2_xboole_0(k2_xboole_0(X22,X23),X24))) )),
% 2.68/0.72    inference(superposition,[],[f37,f242])).
% 2.68/0.72  fof(f242,plain,(
% 2.68/0.72    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 2.68/0.72    inference(forward_demodulation,[],[f235,f117])).
% 2.68/0.72  fof(f117,plain,(
% 2.68/0.72    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 2.68/0.72    inference(resolution,[],[f36,f75])).
% 2.68/0.72  fof(f75,plain,(
% 2.68/0.72    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.68/0.72    inference(superposition,[],[f26,f65])).
% 2.68/0.72  fof(f65,plain,(
% 2.68/0.72    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.68/0.72    inference(superposition,[],[f27,f25])).
% 2.68/0.72  fof(f27,plain,(
% 2.68/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.68/0.72    inference(cnf_transformation,[],[f1])).
% 2.68/0.72  fof(f1,axiom,(
% 2.68/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.68/0.72  fof(f26,plain,(
% 2.68/0.72    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.68/0.72    inference(cnf_transformation,[],[f12])).
% 2.68/0.72  fof(f12,axiom,(
% 2.68/0.72    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.68/0.72  fof(f36,plain,(
% 2.68/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.68/0.72    inference(cnf_transformation,[],[f5])).
% 2.68/0.72  fof(f5,axiom,(
% 2.68/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.68/0.72  fof(f235,plain,(
% 2.68/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 2.68/0.72    inference(superposition,[],[f38,f114])).
% 2.68/0.72  fof(f114,plain,(
% 2.68/0.72    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.68/0.72    inference(resolution,[],[f36,f26])).
% 2.68/0.72  fof(f37,plain,(
% 2.68/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.68/0.72    inference(cnf_transformation,[],[f5])).
% 2.68/0.72  fof(f582,plain,(
% 2.68/0.72    spl5_14 | ~spl5_12),
% 2.68/0.72    inference(avatar_split_clause,[],[f571,f560,f579])).
% 2.68/0.72  fof(f560,plain,(
% 2.68/0.72    spl5_12 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.68/0.72  fof(f571,plain,(
% 2.68/0.72    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl5_12),
% 2.68/0.72    inference(resolution,[],[f562,f30])).
% 2.68/0.72  fof(f562,plain,(
% 2.68/0.72    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl5_12),
% 2.68/0.72    inference(avatar_component_clause,[],[f560])).
% 2.68/0.72  fof(f563,plain,(
% 2.68/0.72    spl5_12 | ~spl5_7),
% 2.68/0.72    inference(avatar_split_clause,[],[f557,f119,f560])).
% 2.68/0.72  fof(f119,plain,(
% 2.68/0.72    spl5_7 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.68/0.72  fof(f557,plain,(
% 2.68/0.72    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl5_7),
% 2.68/0.72    inference(trivial_inequality_removal,[],[f545])).
% 2.68/0.72  fof(f545,plain,(
% 2.68/0.72    k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl5_7),
% 2.68/0.72    inference(superposition,[],[f167,f121])).
% 2.68/0.72  fof(f121,plain,(
% 2.68/0.72    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_7),
% 2.68/0.72    inference(avatar_component_clause,[],[f119])).
% 2.68/0.72  fof(f167,plain,(
% 2.68/0.72    ( ! [X14,X15,X13] : (k1_xboole_0 != k4_xboole_0(X13,k2_xboole_0(X14,X15)) | r1_tarski(k4_xboole_0(X13,X14),X15)) )),
% 2.68/0.72    inference(superposition,[],[f37,f38])).
% 2.68/0.72  fof(f122,plain,(
% 2.68/0.72    spl5_7 | ~spl5_3),
% 2.68/0.72    inference(avatar_split_clause,[],[f113,f60,f119])).
% 2.68/0.72  fof(f60,plain,(
% 2.68/0.72    spl5_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.68/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.68/0.72  fof(f113,plain,(
% 2.68/0.72    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.68/0.72    inference(resolution,[],[f36,f62])).
% 2.68/0.72  fof(f62,plain,(
% 2.68/0.72    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_3),
% 2.68/0.72    inference(avatar_component_clause,[],[f60])).
% 2.68/0.72  fof(f63,plain,(
% 2.68/0.72    spl5_3),
% 2.68/0.72    inference(avatar_split_clause,[],[f22,f60])).
% 2.68/0.72  fof(f22,plain,(
% 2.68/0.72    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 2.68/0.72    inference(cnf_transformation,[],[f16])).
% 2.68/0.72  fof(f16,plain,(
% 2.68/0.72    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.68/0.72    inference(flattening,[],[f15])).
% 2.68/0.72  fof(f15,plain,(
% 2.68/0.72    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.68/0.72    inference(ennf_transformation,[],[f14])).
% 2.68/0.72  fof(f14,negated_conjecture,(
% 2.68/0.72    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.68/0.72    inference(negated_conjecture,[],[f13])).
% 2.68/0.72  fof(f13,conjecture,(
% 2.68/0.72    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 2.68/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 2.68/0.72  fof(f58,plain,(
% 2.68/0.72    spl5_2),
% 2.68/0.72    inference(avatar_split_clause,[],[f23,f55])).
% 2.68/0.72  fof(f23,plain,(
% 2.68/0.72    r1_xboole_0(sK0,sK2)),
% 2.68/0.72    inference(cnf_transformation,[],[f16])).
% 2.68/0.72  fof(f53,plain,(
% 2.68/0.72    ~spl5_1),
% 2.68/0.72    inference(avatar_split_clause,[],[f24,f50])).
% 2.68/0.72  fof(f24,plain,(
% 2.68/0.72    ~r1_tarski(sK0,sK1)),
% 2.68/0.72    inference(cnf_transformation,[],[f16])).
% 2.68/0.72  % SZS output end Proof for theBenchmark
% 2.68/0.72  % (11168)------------------------------
% 2.68/0.72  % (11168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.72  % (11168)Termination reason: Refutation
% 2.68/0.72  
% 2.68/0.72  % (11168)Memory used [KB]: 12665
% 2.68/0.72  % (11168)Time elapsed: 0.274 s
% 2.68/0.72  % (11168)------------------------------
% 2.68/0.72  % (11168)------------------------------
% 2.68/0.72  % (11151)Success in time 0.357 s
%------------------------------------------------------------------------------
