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
% DateTime   : Thu Dec  3 12:55:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 452 expanded)
%              Number of leaves         :   12 ( 127 expanded)
%              Depth                    :   27
%              Number of atoms          :  228 (1930 expanded)
%              Number of equality atoms :   25 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f30,f125,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f36,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f125,plain,(
    ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f48,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f124,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f123,f30])).

fof(f123,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f115,plain,(
    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0) ),
    inference(forward_demodulation,[],[f114,f100])).

fof(f100,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f99,f81])).

fof(f81,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f78,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f70,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f63,f30])).

fof(f63,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f59,f49])).

fof(f59,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f31])).

fof(f31,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f58,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f33,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f78,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f74,f31])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | sK0 = X0
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f99,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f96,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f95,f30])).

% (8540)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f95,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f91,f49])).

fof(f91,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f89,f31])).

fof(f89,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | sK0 = sK1 ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f32,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f103,f39])).

fof(f103,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    inference(backward_demodulation,[],[f47,f100])).

fof(f30,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8532)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (8547)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (8539)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (8531)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8547)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f30,f125,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f124,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f35])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f123,f30])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ~v3_ordinal1(sK0) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 0.21/0.52    inference(resolution,[],[f115,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f40,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f114,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    sK0 = sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0) | sK0 = sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0) | sK0 = sK1 | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f52,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f30])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.52    inference(resolution,[],[f59,f49])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    v3_ordinal1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(resolution,[],[f37,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f35])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f35])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f74,f31])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | sK0 = X0 | r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f38,f30])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    sK0 = sK1 | ~r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f96,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f35])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | sK0 = sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f95,f30])).
% 0.21/0.52  % (8540)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.21/0.52    inference(resolution,[],[f91,f49])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | sK0 = sK1),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f31])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~v3_ordinal1(sK1) | ~v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) | ~r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) | sK0 = sK1),
% 0.21/0.52    inference(resolution,[],[f62,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) | sK0 = sK1),
% 0.21/0.52    inference(resolution,[],[f71,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r2_hidden(sK0,sK1) | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f35])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f39])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    r2_hidden(sK0,sK0) | r1_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f47,f100])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v3_ordinal1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8547)------------------------------
% 0.21/0.52  % (8547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8547)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8547)Memory used [KB]: 6268
% 0.21/0.52  % (8547)Time elapsed: 0.068 s
% 0.21/0.52  % (8547)------------------------------
% 0.21/0.52  % (8547)------------------------------
% 0.21/0.52  % (8524)Success in time 0.16 s
%------------------------------------------------------------------------------
