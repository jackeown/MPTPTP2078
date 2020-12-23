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
% DateTime   : Thu Dec  3 12:55:28 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 411 expanded)
%              Number of leaves         :   14 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 749 expanded)
%              Number of equality atoms :   14 ( 225 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f304,f277])).

fof(f277,plain,(
    ~ r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    inference(subsumption_resolution,[],[f276,f108])).

fof(f108,plain,(
    v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f57,f31])).

fof(f31,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f34,f51,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f276,plain,
    ( ~ r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(subsumption_resolution,[],[f275,f30])).

fof(f30,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f275,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f218,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f218,plain,(
    ~ r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    inference(resolution,[],[f217,f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    inference(definition_unfolding,[],[f29,f53])).

fof(f29,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f217,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f216,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),X2)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f56,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f32,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f216,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f103,f108])).

fof(f103,plain,
    ( ~ v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,
    ( r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f28,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f304,plain,(
    r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ),
    inference(resolution,[],[f235,f222])).

fof(f222,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f221,f85])).

fof(f85,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f84,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f82,f74])).

fof(f82,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f66,f31])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,sK1)
      | r1_ordinal1(sK1,X0) ) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f79,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f75,f30])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X1,sK0)
      | ~ r1_ordinal1(X1,sK0) ) ),
    inference(resolution,[],[f40,f31])).

fof(f221,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f217,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) ) ),
    inference(resolution,[],[f219,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f219,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f217,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n015.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 16:19:23 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.47  % (19071)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.17/0.48  % (19068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.17/0.48  % (19077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.17/0.48  % (19085)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.17/0.48  % (19070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.17/0.49  % (19065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.17/0.49  % (19063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.17/0.49  % (19068)Refutation found. Thanks to Tanya!
% 0.17/0.49  % SZS status Theorem for theBenchmark
% 0.17/0.49  % SZS output start Proof for theBenchmark
% 0.17/0.49  fof(f305,plain,(
% 0.17/0.49    $false),
% 0.17/0.49    inference(subsumption_resolution,[],[f304,f277])).
% 0.17/0.49  fof(f277,plain,(
% 0.17/0.49    ~r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.17/0.49    inference(subsumption_resolution,[],[f276,f108])).
% 0.17/0.49  fof(f108,plain,(
% 0.17/0.49    v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.17/0.49    inference(resolution,[],[f57,f31])).
% 0.17/0.49  fof(f31,plain,(
% 0.17/0.49    v3_ordinal1(sK0)),
% 0.17/0.49    inference(cnf_transformation,[],[f17])).
% 0.17/0.49  fof(f17,plain,(
% 0.17/0.49    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.17/0.49    inference(ennf_transformation,[],[f16])).
% 0.17/0.49  fof(f16,negated_conjecture,(
% 0.17/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.17/0.49    inference(negated_conjecture,[],[f15])).
% 0.17/0.49  fof(f15,conjecture,(
% 0.17/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.17/0.49  fof(f57,plain,(
% 0.17/0.49    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 0.17/0.49    inference(definition_unfolding,[],[f35,f53])).
% 0.17/0.49  fof(f53,plain,(
% 0.17/0.49    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 0.17/0.49    inference(definition_unfolding,[],[f34,f51,f52])).
% 0.17/0.49  fof(f52,plain,(
% 0.17/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.17/0.49    inference(definition_unfolding,[],[f33,f50])).
% 0.17/0.49  fof(f50,plain,(
% 0.17/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.17/0.49    inference(definition_unfolding,[],[f37,f47])).
% 0.17/0.49  fof(f47,plain,(
% 0.17/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f6])).
% 0.17/0.49  fof(f6,axiom,(
% 0.17/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.17/0.49  fof(f37,plain,(
% 0.17/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f5])).
% 0.17/0.49  fof(f5,axiom,(
% 0.17/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.49  fof(f33,plain,(
% 0.17/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f4])).
% 0.17/0.49  fof(f4,axiom,(
% 0.17/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.49  fof(f51,plain,(
% 0.17/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.17/0.49    inference(definition_unfolding,[],[f36,f50])).
% 0.17/0.49  fof(f36,plain,(
% 0.17/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f8])).
% 0.17/0.49  fof(f8,axiom,(
% 0.17/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.17/0.49  fof(f34,plain,(
% 0.17/0.49    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f10])).
% 0.17/0.49  fof(f10,axiom,(
% 0.17/0.49    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.17/0.49  fof(f35,plain,(
% 0.17/0.49    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f18])).
% 0.17/0.49  fof(f18,plain,(
% 0.17/0.49    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.17/0.49    inference(ennf_transformation,[],[f13])).
% 0.17/0.49  fof(f13,axiom,(
% 0.17/0.49    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.17/0.49  fof(f276,plain,(
% 0.17/0.49    ~r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.17/0.49    inference(subsumption_resolution,[],[f275,f30])).
% 0.17/0.49  fof(f30,plain,(
% 0.17/0.49    v3_ordinal1(sK1)),
% 0.17/0.49    inference(cnf_transformation,[],[f17])).
% 0.17/0.49  fof(f275,plain,(
% 0.17/0.49    ~v3_ordinal1(sK1) | ~r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | ~v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.17/0.49    inference(resolution,[],[f218,f39])).
% 0.17/0.49  fof(f39,plain,(
% 0.17/0.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f22])).
% 0.17/0.49  fof(f22,plain,(
% 0.17/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.17/0.49    inference(flattening,[],[f21])).
% 0.17/0.49  fof(f21,plain,(
% 0.17/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.17/0.49    inference(ennf_transformation,[],[f11])).
% 0.17/0.49  fof(f11,axiom,(
% 0.17/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.17/0.49  fof(f218,plain,(
% 0.17/0.49    ~r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.17/0.49    inference(resolution,[],[f217,f54])).
% 0.17/0.49  fof(f54,plain,(
% 0.17/0.49    ~r2_hidden(sK0,sK1) | ~r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.17/0.49    inference(definition_unfolding,[],[f29,f53])).
% 0.17/0.49  fof(f29,plain,(
% 0.17/0.49    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(cnf_transformation,[],[f17])).
% 0.17/0.49  fof(f217,plain,(
% 0.17/0.49    r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(subsumption_resolution,[],[f216,f105])).
% 0.17/0.49  fof(f105,plain,(
% 0.17/0.49    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),X2) | r2_hidden(X1,X2)) )),
% 0.17/0.49    inference(resolution,[],[f56,f41])).
% 0.17/0.49  fof(f41,plain,(
% 0.17/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f23])).
% 0.17/0.49  fof(f23,plain,(
% 0.17/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.17/0.49    inference(ennf_transformation,[],[f1])).
% 0.17/0.49  fof(f1,axiom,(
% 0.17/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.17/0.49  fof(f56,plain,(
% 0.17/0.49    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 0.17/0.49    inference(definition_unfolding,[],[f32,f53])).
% 0.17/0.49  fof(f32,plain,(
% 0.17/0.49    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.17/0.49    inference(cnf_transformation,[],[f12])).
% 0.17/0.49  fof(f12,axiom,(
% 0.17/0.49    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.17/0.49  fof(f216,plain,(
% 0.17/0.49    r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(resolution,[],[f103,f108])).
% 0.17/0.49  fof(f103,plain,(
% 0.17/0.49    ~v3_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0)))) | r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(resolution,[],[f55,f74])).
% 0.17/0.49  fof(f74,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.17/0.49    inference(resolution,[],[f40,f30])).
% 0.17/0.49  fof(f40,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f22])).
% 0.17/0.49  fof(f55,plain,(
% 0.17/0.49    r1_ordinal1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(definition_unfolding,[],[f28,f53])).
% 0.17/0.49  fof(f28,plain,(
% 0.17/0.49    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.17/0.49    inference(cnf_transformation,[],[f17])).
% 0.17/0.49  fof(f304,plain,(
% 0.17/0.49    r1_tarski(k3_tarski(k2_enumset1(sK0,sK0,sK0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)),
% 0.17/0.49    inference(resolution,[],[f235,f222])).
% 0.17/0.49  fof(f222,plain,(
% 0.17/0.49    r1_tarski(sK0,sK1)),
% 0.17/0.49    inference(resolution,[],[f221,f85])).
% 0.17/0.49  fof(f85,plain,(
% 0.17/0.49    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.17/0.49    inference(subsumption_resolution,[],[f84,f31])).
% 0.17/0.49  fof(f84,plain,(
% 0.17/0.49    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.17/0.49    inference(resolution,[],[f82,f74])).
% 0.17/0.49  fof(f82,plain,(
% 0.17/0.49    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.17/0.49    inference(resolution,[],[f79,f69])).
% 0.17/0.49  fof(f69,plain,(
% 0.17/0.49    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.17/0.49    inference(resolution,[],[f66,f31])).
% 0.17/0.49  fof(f66,plain,(
% 0.17/0.49    ( ! [X0] : (~v3_ordinal1(X0) | r1_ordinal1(X0,sK1) | r1_ordinal1(sK1,X0)) )),
% 0.17/0.49    inference(resolution,[],[f38,f30])).
% 0.17/0.49  fof(f38,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f20])).
% 0.17/0.49  fof(f20,plain,(
% 0.17/0.49    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.17/0.49    inference(flattening,[],[f19])).
% 0.17/0.49  fof(f19,plain,(
% 0.17/0.49    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.17/0.49    inference(ennf_transformation,[],[f9])).
% 0.17/0.49  fof(f9,axiom,(
% 0.17/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.17/0.49  fof(f79,plain,(
% 0.17/0.49    ~r1_ordinal1(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.17/0.49    inference(resolution,[],[f75,f30])).
% 0.17/0.49  fof(f75,plain,(
% 0.17/0.49    ( ! [X1] : (~v3_ordinal1(X1) | r1_tarski(X1,sK0) | ~r1_ordinal1(X1,sK0)) )),
% 0.17/0.49    inference(resolution,[],[f40,f31])).
% 0.17/0.49  fof(f221,plain,(
% 0.17/0.49    ~r1_tarski(sK1,sK0)),
% 0.17/0.49    inference(resolution,[],[f217,f46])).
% 0.17/0.49  fof(f46,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f24])).
% 0.17/0.49  fof(f24,plain,(
% 0.17/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.17/0.49    inference(ennf_transformation,[],[f14])).
% 0.17/0.49  fof(f14,axiom,(
% 0.17/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.17/0.49  fof(f235,plain,(
% 0.17/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK0,sK0,sK0,sK0))),sK1)) )),
% 0.17/0.49    inference(resolution,[],[f219,f61])).
% 0.17/0.49  fof(f61,plain,(
% 0.17/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)) )),
% 0.17/0.49    inference(definition_unfolding,[],[f49,f51])).
% 0.17/0.49  fof(f49,plain,(
% 0.17/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f27])).
% 0.17/0.49  fof(f27,plain,(
% 0.17/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.17/0.49    inference(flattening,[],[f26])).
% 0.17/0.49  fof(f26,plain,(
% 0.17/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.17/0.49    inference(ennf_transformation,[],[f3])).
% 0.17/0.49  fof(f3,axiom,(
% 0.17/0.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.17/0.49  fof(f219,plain,(
% 0.17/0.49    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.17/0.49    inference(resolution,[],[f217,f59])).
% 0.17/0.49  fof(f59,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.17/0.49    inference(definition_unfolding,[],[f44,f52])).
% 0.17/0.49  fof(f44,plain,(
% 0.17/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.17/0.49    inference(cnf_transformation,[],[f7])).
% 0.17/0.49  fof(f7,axiom,(
% 0.17/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.17/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.17/0.49  % SZS output end Proof for theBenchmark
% 0.17/0.49  % (19068)------------------------------
% 0.17/0.49  % (19068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (19068)Termination reason: Refutation
% 0.17/0.49  
% 0.17/0.49  % (19068)Memory used [KB]: 6396
% 0.17/0.49  % (19068)Time elapsed: 0.128 s
% 0.17/0.49  % (19068)------------------------------
% 0.17/0.49  % (19068)------------------------------
% 0.17/0.49  % (19069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.17/0.50  % (19088)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.17/0.50  % (19062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.17/0.50  % (19061)Success in time 0.182 s
%------------------------------------------------------------------------------
