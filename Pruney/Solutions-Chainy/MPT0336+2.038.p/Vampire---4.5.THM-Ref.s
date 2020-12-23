%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 120 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 303 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(subsumption_resolution,[],[f340,f147])).

fof(f147,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f71,f24])).

fof(f24,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f71,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f25,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f340,plain,(
    r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f170,f332])).

fof(f332,plain,(
    sK3 = sK4(sK1,sK0) ),
    inference(resolution,[],[f271,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f271,plain,(
    r2_hidden(sK4(sK1,sK0),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f264,f115])).

fof(f115,plain,(
    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f114,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f114,plain,(
    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f108,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f108,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f101,f70])).

fof(f70,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f101,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f81,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f26,f36])).

fof(f26,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f264,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(sK0,sK1))
      | r2_hidden(X5,k2_enumset1(sK3,sK3,sK3,sK3)) ) ),
    inference(superposition,[],[f62,f126])).

fof(f126,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f23,f52])).

fof(f23,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f170,plain,(
    r2_hidden(sK4(sK1,sK0),sK1) ),
    inference(resolution,[],[f115,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (31202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  % (31199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (31218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.51  % (31196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (31201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (31205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (31216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (31217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (31195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (31220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (31221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (31208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (31197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (31206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (31198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (31209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.53  % (31212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.54  % (31211)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  % (31207)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.54  % (31200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (31211)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f343,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(subsumption_resolution,[],[f340,f147])).
% 0.19/0.54  fof(f147,plain,(
% 0.19/0.54    ~r2_hidden(sK3,sK1)),
% 0.19/0.54    inference(resolution,[],[f71,f24])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    r2_hidden(sK3,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.19/0.54    inference(flattening,[],[f16])).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.19/0.54    inference(ennf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.54    inference(negated_conjecture,[],[f12])).
% 0.19/0.54  fof(f12,conjecture,(
% 0.19/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.19/0.54  fof(f71,plain,(
% 0.19/0.54    ( ! [X2] : (~r2_hidden(X2,sK2) | ~r2_hidden(X2,sK1)) )),
% 0.19/0.54    inference(resolution,[],[f25,f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.54    inference(rectify,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    r1_xboole_0(sK2,sK1)),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f340,plain,(
% 0.19/0.54    r2_hidden(sK3,sK1)),
% 0.19/0.54    inference(backward_demodulation,[],[f170,f332])).
% 0.19/0.54  fof(f332,plain,(
% 0.19/0.54    sK3 = sK4(sK1,sK0)),
% 0.19/0.54    inference(resolution,[],[f271,f58])).
% 0.19/0.54  fof(f58,plain,(
% 0.19/0.54    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))) )),
% 0.19/0.54    inference(equality_resolution,[],[f56])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.19/0.54    inference(definition_unfolding,[],[f38,f52])).
% 0.19/0.54  fof(f52,plain,(
% 0.19/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f27,f51])).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f29,f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,axiom,(
% 0.19/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,axiom,(
% 0.19/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.54  fof(f271,plain,(
% 0.19/0.54    r2_hidden(sK4(sK1,sK0),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.19/0.54    inference(resolution,[],[f264,f115])).
% 0.19/0.54  fof(f115,plain,(
% 0.19/0.54    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(forward_demodulation,[],[f114,f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.54  fof(f114,plain,(
% 0.19/0.54    r2_hidden(sK4(sK1,sK0),k3_xboole_0(sK1,sK0))),
% 0.19/0.54    inference(resolution,[],[f108,f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.54    inference(rectify,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.54  fof(f108,plain,(
% 0.19/0.54    ~r1_xboole_0(sK1,sK0)),
% 0.19/0.54    inference(subsumption_resolution,[],[f101,f70])).
% 0.19/0.54  fof(f70,plain,(
% 0.19/0.54    r1_xboole_0(sK1,sK2)),
% 0.19/0.54    inference(resolution,[],[f25,f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.54  fof(f101,plain,(
% 0.19/0.54    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 0.19/0.54    inference(resolution,[],[f81,f44])).
% 0.19/0.54  fof(f44,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.19/0.54  fof(f81,plain,(
% 0.19/0.54    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.19/0.54    inference(resolution,[],[f26,f36])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f264,plain,(
% 0.19/0.54    ( ! [X5] : (~r2_hidden(X5,k3_xboole_0(sK0,sK1)) | r2_hidden(X5,k2_enumset1(sK3,sK3,sK3,sK3))) )),
% 0.19/0.54    inference(superposition,[],[f62,f126])).
% 0.19/0.54  fof(f126,plain,(
% 0.19/0.54    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.19/0.54    inference(resolution,[],[f53,f35])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f20])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.19/0.54    inference(definition_unfolding,[],[f23,f52])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(equality_resolution,[],[f49])).
% 0.19/0.54  fof(f49,plain,(
% 0.19/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.19/0.54  fof(f170,plain,(
% 0.19/0.54    r2_hidden(sK4(sK1,sK0),sK1)),
% 0.19/0.54    inference(resolution,[],[f115,f62])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (31211)------------------------------
% 0.19/0.54  % (31211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31211)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (31211)Memory used [KB]: 1791
% 0.19/0.54  % (31211)Time elapsed: 0.129 s
% 0.19/0.54  % (31211)------------------------------
% 0.19/0.54  % (31211)------------------------------
% 0.19/0.54  % (31222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.54  % (31223)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.54  % (31193)Success in time 0.189 s
%------------------------------------------------------------------------------
