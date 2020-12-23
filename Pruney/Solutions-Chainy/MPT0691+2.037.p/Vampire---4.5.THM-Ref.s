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
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 193 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  119 ( 491 expanded)
%              Number of equality atoms :   35 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(resolution,[],[f233,f38])).

fof(f38,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f233,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f230,f184])).

fof(f184,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f170,f37])).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f132,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f83,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X0)))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    inference(superposition,[],[f51,f78])).

fof(f78,plain,(
    ! [X1] : k3_xboole_0(X1,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X1)) ),
    inference(superposition,[],[f57,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X3] : k1_relat_1(k7_relat_1(sK1,X3)) = k3_xboole_0(k1_relat_1(sK1),X3) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f83,plain,(
    ! [X4,X3] :
      ( r1_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3)))
      | ~ r1_tarski(X4,X3)
      | ~ r1_tarski(X4,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f49,f57])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f230,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f219,f106])).

fof(f106,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) ),
    inference(superposition,[],[f105,f55])).

fof(f55,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK1,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK1,X2)) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f105,plain,(
    ! [X5] : k1_relat_1(k7_relat_1(sK1,X5)) = k10_relat_1(k7_relat_1(sK1,X5),k9_relat_1(sK1,X5)) ),
    inference(forward_demodulation,[],[f62,f58])).

fof(f58,plain,(
    ! [X4] : k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f62,plain,(
    ! [X5] : k10_relat_1(k7_relat_1(sK1,X5),k2_relat_1(k7_relat_1(sK1,X5))) = k1_relat_1(k7_relat_1(sK1,X5)) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f219,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),X0) ),
    inference(superposition,[],[f138,f186])).

fof(f186,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[],[f63,f184])).

fof(f63,plain,(
    ! [X6,X7] : k1_relat_1(k7_relat_1(k7_relat_1(sK1,X6),X7)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X6)),X7) ),
    inference(resolution,[],[f54,f41])).

fof(f138,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0)),X0) ),
    inference(superposition,[],[f51,f116])).

fof(f116,plain,(
    ! [X2,X3] : k3_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3)) ),
    inference(superposition,[],[f63,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:36:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.49  % (18443)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (18442)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (18457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (18451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (18460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (18465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (18445)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (18465)Refutation not found, incomplete strategy% (18465)------------------------------
% 0.20/0.51  % (18465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18463)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (18446)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (18449)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (18465)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18465)Memory used [KB]: 10746
% 0.20/0.52  % (18465)Time elapsed: 0.106 s
% 0.20/0.52  % (18465)------------------------------
% 0.20/0.52  % (18465)------------------------------
% 0.20/0.52  % (18452)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.53  % (18440)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.39/0.53  % (18439)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.53  % (18441)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.53  % (18444)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.53  % (18454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.53  % (18461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.53  % (18448)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.54  % (18462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.54  % (18437)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.54  % (18456)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.54  % (18455)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.54  % (18453)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.55  % (18453)Refutation not found, incomplete strategy% (18453)------------------------------
% 1.50/0.55  % (18453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (18453)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (18453)Memory used [KB]: 10618
% 1.50/0.55  % (18453)Time elapsed: 0.150 s
% 1.50/0.55  % (18453)------------------------------
% 1.50/0.55  % (18453)------------------------------
% 1.50/0.55  % (18438)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.55  % (18466)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.55  % (18459)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.50/0.55  % (18450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.55  % (18438)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f234,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(resolution,[],[f233,f38])).
% 1.50/0.55  fof(f38,plain,(
% 1.50/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.55    inference(cnf_transformation,[],[f33])).
% 1.50/0.55  fof(f33,plain,(
% 1.50/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f32])).
% 1.50/0.55  fof(f32,plain,(
% 1.50/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f21,plain,(
% 1.50/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.50/0.55    inference(flattening,[],[f20])).
% 1.50/0.55  fof(f20,plain,(
% 1.50/0.55    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f19])).
% 1.50/0.55  fof(f19,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.55    inference(negated_conjecture,[],[f18])).
% 1.50/0.55  fof(f18,conjecture,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.50/0.55  fof(f233,plain,(
% 1.50/0.55    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.55    inference(forward_demodulation,[],[f230,f184])).
% 1.50/0.55  fof(f184,plain,(
% 1.50/0.55    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.55    inference(resolution,[],[f170,f37])).
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.50/0.55    inference(cnf_transformation,[],[f33])).
% 1.50/0.55  fof(f170,plain,(
% 1.50/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.50/0.55    inference(resolution,[],[f132,f53])).
% 1.50/0.55  fof(f53,plain,(
% 1.50/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.55    inference(equality_resolution,[],[f43])).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.50/0.55    inference(cnf_transformation,[],[f35])).
% 1.50/0.55  fof(f35,plain,(
% 1.50/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.55    inference(flattening,[],[f34])).
% 1.50/0.55  fof(f34,plain,(
% 1.50/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.55    inference(nnf_transformation,[],[f2])).
% 1.50/0.55  fof(f2,axiom,(
% 1.50/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.55  fof(f132,plain,(
% 1.50/0.55    ( ! [X0] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.50/0.55    inference(resolution,[],[f83,f91])).
% 1.50/0.55  fof(f91,plain,(
% 1.50/0.55    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X0))) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.50/0.55    inference(resolution,[],[f87,f45])).
% 1.50/0.55  fof(f45,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.50/0.55    inference(cnf_transformation,[],[f35])).
% 1.50/0.55  fof(f87,plain,(
% 1.50/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) )),
% 1.50/0.55    inference(superposition,[],[f51,f78])).
% 1.50/0.55  fof(f78,plain,(
% 1.50/0.55    ( ! [X1] : (k3_xboole_0(X1,k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.50/0.55    inference(superposition,[],[f57,f50])).
% 1.50/0.55  fof(f50,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.50/0.55  fof(f57,plain,(
% 1.50/0.55    ( ! [X3] : (k1_relat_1(k7_relat_1(sK1,X3)) = k3_xboole_0(k1_relat_1(sK1),X3)) )),
% 1.50/0.55    inference(resolution,[],[f36,f41])).
% 1.50/0.55  fof(f41,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f16])).
% 1.50/0.55  fof(f16,axiom,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    v1_relat_1(sK1)),
% 1.50/0.55    inference(cnf_transformation,[],[f33])).
% 1.50/0.55  fof(f51,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f6])).
% 1.50/0.55  fof(f6,axiom,(
% 1.50/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.50/0.55  fof(f83,plain,(
% 1.50/0.55    ( ! [X4,X3] : (r1_tarski(X4,k1_relat_1(k7_relat_1(sK1,X3))) | ~r1_tarski(X4,X3) | ~r1_tarski(X4,k1_relat_1(sK1))) )),
% 1.50/0.55    inference(superposition,[],[f49,f57])).
% 1.50/0.55  fof(f49,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f31])).
% 1.50/0.55  fof(f31,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.55    inference(flattening,[],[f30])).
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.55    inference(ennf_transformation,[],[f7])).
% 1.50/0.55  fof(f7,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.50/0.55  fof(f230,plain,(
% 1.50/0.55    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.55    inference(superposition,[],[f219,f106])).
% 1.50/0.55  fof(f106,plain,(
% 1.50/0.55    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) )),
% 1.50/0.55    inference(superposition,[],[f105,f55])).
% 1.50/0.55  fof(f55,plain,(
% 1.50/0.55    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK1,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK1,X2))) )),
% 1.50/0.55    inference(resolution,[],[f36,f47])).
% 1.50/0.55  fof(f47,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.50/0.55    inference(ennf_transformation,[],[f17])).
% 1.50/0.55  fof(f17,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.50/0.55  fof(f105,plain,(
% 1.50/0.55    ( ! [X5] : (k1_relat_1(k7_relat_1(sK1,X5)) = k10_relat_1(k7_relat_1(sK1,X5),k9_relat_1(sK1,X5))) )),
% 1.50/0.55    inference(forward_demodulation,[],[f62,f58])).
% 1.50/0.55  fof(f58,plain,(
% 1.50/0.55    ( ! [X4] : (k2_relat_1(k7_relat_1(sK1,X4)) = k9_relat_1(sK1,X4)) )),
% 1.50/0.55    inference(resolution,[],[f36,f40])).
% 1.50/0.55  fof(f40,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f24])).
% 1.50/0.55  fof(f24,plain,(
% 1.50/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.55    inference(ennf_transformation,[],[f12])).
% 1.50/0.55  fof(f12,axiom,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.50/0.55  fof(f62,plain,(
% 1.50/0.55    ( ! [X5] : (k10_relat_1(k7_relat_1(sK1,X5),k2_relat_1(k7_relat_1(sK1,X5))) = k1_relat_1(k7_relat_1(sK1,X5))) )),
% 1.50/0.55    inference(resolution,[],[f54,f46])).
% 1.50/0.55  fof(f46,plain,(
% 1.50/0.55    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.55    inference(ennf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,axiom,(
% 1.50/0.55    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.50/0.55  fof(f54,plain,(
% 1.50/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.50/0.55    inference(resolution,[],[f36,f48])).
% 1.50/0.55  fof(f48,plain,(
% 1.50/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f29])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.55    inference(ennf_transformation,[],[f11])).
% 1.50/0.55  fof(f11,axiom,(
% 1.50/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.50/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.50/0.55  fof(f219,plain,(
% 1.50/0.55    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),X0)) )),
% 1.50/0.55    inference(superposition,[],[f138,f186])).
% 1.50/0.55  fof(f186,plain,(
% 1.50/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0)) )),
% 1.50/0.55    inference(superposition,[],[f63,f184])).
% 1.50/0.55  fof(f63,plain,(
% 1.50/0.55    ( ! [X6,X7] : (k1_relat_1(k7_relat_1(k7_relat_1(sK1,X6),X7)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X6)),X7)) )),
% 1.50/0.55    inference(resolution,[],[f54,f41])).
% 1.50/0.55  fof(f138,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0)),X0)) )),
% 1.50/0.55    inference(superposition,[],[f51,f116])).
% 1.50/0.55  fof(f116,plain,(
% 1.50/0.55    ( ! [X2,X3] : (k3_xboole_0(X3,k1_relat_1(k7_relat_1(sK1,X2))) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X2),X3))) )),
% 1.50/0.55    inference(superposition,[],[f63,f50])).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (18438)------------------------------
% 1.50/0.55  % (18438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (18438)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (18438)Memory used [KB]: 1791
% 1.50/0.55  % (18438)Time elapsed: 0.147 s
% 1.50/0.55  % (18438)------------------------------
% 1.50/0.55  % (18438)------------------------------
% 1.50/0.55  % (18447)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (18464)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.56  % (18458)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.57  % (18447)Refutation not found, incomplete strategy% (18447)------------------------------
% 1.50/0.57  % (18447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (18436)Success in time 0.222 s
%------------------------------------------------------------------------------
