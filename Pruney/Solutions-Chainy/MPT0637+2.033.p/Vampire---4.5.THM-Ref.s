%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:26 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 125 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 204 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(resolution,[],[f605,f333])).

fof(f333,plain,(
    ~ r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f221,f233,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f233,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f88,f127])).

fof(f127,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f122,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f122,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f55,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f221,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f30,f79])).

fof(f30,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f605,plain,(
    ! [X2,X3] : r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f186,f117])).

fof(f117,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f114,f41])).

fof(f114,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f43,f48,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f186,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f90,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f179,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2)) ),
    inference(backward_demodulation,[],[f95,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2)) ),
    inference(unit_resulting_resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f80,f79])).

fof(f80,plain,(
    ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f43,f43,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f179,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f178,f79])).

fof(f178,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f145,f79])).

fof(f145,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(unit_resulting_resolution,[],[f43,f43,f43,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f90,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f58,f79])).

fof(f58,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f52,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (12487)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.49  % (12508)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.49  % (12499)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.49  % (12491)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (12507)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (12498)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (12498)Refutation not found, incomplete strategy% (12498)------------------------------
% 0.22/0.52  % (12498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12488)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (12498)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12498)Memory used [KB]: 1663
% 0.22/0.52  % (12498)Time elapsed: 0.057 s
% 0.22/0.52  % (12498)------------------------------
% 0.22/0.52  % (12498)------------------------------
% 0.22/0.53  % (12490)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12497)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (12489)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (12511)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (12485)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (12485)Refutation not found, incomplete strategy% (12485)------------------------------
% 0.22/0.55  % (12485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12485)Memory used [KB]: 1663
% 0.22/0.55  % (12485)Time elapsed: 0.133 s
% 0.22/0.55  % (12485)------------------------------
% 0.22/0.55  % (12485)------------------------------
% 0.22/0.55  % (12512)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (12512)Refutation not found, incomplete strategy% (12512)------------------------------
% 0.22/0.55  % (12512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12512)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12512)Memory used [KB]: 6140
% 0.22/0.55  % (12512)Time elapsed: 0.135 s
% 0.22/0.55  % (12503)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (12512)------------------------------
% 0.22/0.55  % (12512)------------------------------
% 0.22/0.55  % (12503)Refutation not found, incomplete strategy% (12503)------------------------------
% 0.22/0.55  % (12503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (12503)Memory used [KB]: 1663
% 0.22/0.55  % (12503)Time elapsed: 0.137 s
% 0.22/0.55  % (12503)------------------------------
% 0.22/0.55  % (12503)------------------------------
% 0.22/0.55  % (12484)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (12486)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (12504)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (12495)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (12510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (12492)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.56  % (12502)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.56  % (12493)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (12494)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (12514)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.56  % (12514)Refutation not found, incomplete strategy% (12514)------------------------------
% 1.42/0.56  % (12514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (12514)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (12514)Memory used [KB]: 1663
% 1.42/0.56  % (12514)Time elapsed: 0.001 s
% 1.42/0.56  % (12514)------------------------------
% 1.42/0.56  % (12514)------------------------------
% 1.42/0.56  % (12509)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.56  % (12494)Refutation not found, incomplete strategy% (12494)------------------------------
% 1.42/0.56  % (12494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12501)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.57  % (12511)Refutation not found, incomplete strategy% (12511)------------------------------
% 1.42/0.57  % (12511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12511)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12511)Memory used [KB]: 6140
% 1.42/0.57  % (12511)Time elapsed: 0.157 s
% 1.42/0.57  % (12511)------------------------------
% 1.42/0.57  % (12511)------------------------------
% 1.42/0.57  % (12494)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12494)Memory used [KB]: 10618
% 1.42/0.57  % (12494)Time elapsed: 0.149 s
% 1.42/0.57  % (12494)------------------------------
% 1.42/0.57  % (12494)------------------------------
% 1.42/0.57  % (12495)Refutation not found, incomplete strategy% (12495)------------------------------
% 1.42/0.57  % (12495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12495)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12495)Memory used [KB]: 6140
% 1.42/0.57  % (12495)Time elapsed: 0.159 s
% 1.42/0.57  % (12495)------------------------------
% 1.42/0.57  % (12495)------------------------------
% 1.42/0.57  % (12502)Refutation not found, incomplete strategy% (12502)------------------------------
% 1.42/0.57  % (12502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12502)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12502)Memory used [KB]: 1663
% 1.42/0.57  % (12502)Time elapsed: 0.157 s
% 1.42/0.57  % (12502)------------------------------
% 1.42/0.57  % (12502)------------------------------
% 1.42/0.57  % (12510)Refutation not found, incomplete strategy% (12510)------------------------------
% 1.42/0.57  % (12510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12510)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12510)Memory used [KB]: 6140
% 1.42/0.57  % (12510)Time elapsed: 0.157 s
% 1.42/0.57  % (12510)------------------------------
% 1.42/0.57  % (12510)------------------------------
% 1.42/0.57  % (12506)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.57  % (12509)Refutation not found, incomplete strategy% (12509)------------------------------
% 1.42/0.57  % (12509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12509)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12509)Memory used [KB]: 10618
% 1.42/0.57  % (12509)Time elapsed: 0.157 s
% 1.42/0.57  % (12509)------------------------------
% 1.42/0.57  % (12509)------------------------------
% 1.42/0.57  % (12501)Refutation not found, incomplete strategy% (12501)------------------------------
% 1.42/0.57  % (12501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (12501)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (12501)Memory used [KB]: 10618
% 1.42/0.57  % (12501)Time elapsed: 0.155 s
% 1.42/0.57  % (12501)------------------------------
% 1.42/0.57  % (12501)------------------------------
% 1.69/0.58  % (12513)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.69/0.58  % (12496)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.69/0.58  % (12505)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.58  % (12496)Refutation not found, incomplete strategy% (12496)------------------------------
% 1.69/0.58  % (12496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (12496)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (12496)Memory used [KB]: 10618
% 1.69/0.58  % (12496)Time elapsed: 0.142 s
% 1.69/0.58  % (12496)------------------------------
% 1.69/0.58  % (12496)------------------------------
% 1.69/0.59  % (12504)Refutation found. Thanks to Tanya!
% 1.69/0.59  % SZS status Theorem for theBenchmark
% 1.69/0.59  % SZS output start Proof for theBenchmark
% 1.69/0.59  fof(f729,plain,(
% 1.69/0.59    $false),
% 1.69/0.59    inference(resolution,[],[f605,f333])).
% 1.69/0.59  fof(f333,plain,(
% 1.69/0.59    ~r1_tarski(k6_relat_1(k3_xboole_0(sK0,sK1)),k7_relat_1(k6_relat_1(sK0),sK1))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f221,f233,f47])).
% 1.69/0.59  fof(f47,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.59  fof(f233,plain,(
% 1.69/0.59    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 1.69/0.59    inference(superposition,[],[f88,f127])).
% 1.69/0.59  fof(f127,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f122,f41])).
% 1.69/0.59  fof(f41,plain,(
% 1.69/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f12])).
% 1.69/0.59  fof(f12,axiom,(
% 1.69/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.69/0.59  fof(f122,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f34])).
% 1.69/0.59  fof(f34,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f22,plain,(
% 1.69/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f10])).
% 1.69/0.59  fof(f10,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 1.69/0.59  fof(f43,plain,(
% 1.69/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f8])).
% 1.69/0.59  fof(f8,axiom,(
% 1.69/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.69/0.59  fof(f88,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 1.69/0.59    inference(backward_demodulation,[],[f55,f79])).
% 1.69/0.59  fof(f79,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f39])).
% 1.69/0.59  fof(f39,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f15])).
% 1.69/0.59  fof(f15,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.69/0.59  fof(f55,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f37])).
% 1.69/0.59  fof(f37,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f13])).
% 1.69/0.59  fof(f13,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.69/0.59  fof(f221,plain,(
% 1.69/0.59    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.69/0.59    inference(superposition,[],[f30,f79])).
% 1.69/0.59  fof(f30,plain,(
% 1.69/0.59    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.69/0.59    inference(cnf_transformation,[],[f19])).
% 1.69/0.59  fof(f19,plain,(
% 1.69/0.59    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f18])).
% 1.69/0.59  fof(f18,negated_conjecture,(
% 1.69/0.59    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.69/0.59    inference(negated_conjecture,[],[f17])).
% 1.69/0.59  fof(f17,conjecture,(
% 1.69/0.59    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.69/0.59  fof(f605,plain,(
% 1.69/0.59    ( ! [X2,X3] : (r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.69/0.59    inference(superposition,[],[f186,f117])).
% 1.69/0.59  fof(f117,plain,(
% 1.69/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.69/0.59    inference(forward_demodulation,[],[f114,f41])).
% 1.69/0.59  fof(f114,plain,(
% 1.69/0.59    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f48,f44])).
% 1.69/0.59  fof(f44,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f29])).
% 1.69/0.59  fof(f29,plain,(
% 1.69/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(flattening,[],[f28])).
% 1.69/0.59  fof(f28,plain,(
% 1.69/0.59    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f16])).
% 1.69/0.59  fof(f16,axiom,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.69/0.59  fof(f48,plain,(
% 1.69/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.59    inference(equality_resolution,[],[f46])).
% 1.69/0.59  fof(f46,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f2])).
% 1.69/0.59  fof(f186,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.69/0.59    inference(backward_demodulation,[],[f90,f180])).
% 1.69/0.59  fof(f180,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k3_xboole_0(X1,X0))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f179,f138])).
% 1.69/0.59  fof(f138,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X0,X2))) )),
% 1.69/0.59    inference(backward_demodulation,[],[f95,f129])).
% 1.69/0.59  fof(f129,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X1,X2))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f33])).
% 1.69/0.59  fof(f33,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f21])).
% 1.69/0.59  fof(f21,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.69/0.59    inference(ennf_transformation,[],[f9])).
% 1.69/0.59  fof(f9,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.69/0.59  fof(f95,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.69/0.59    inference(backward_demodulation,[],[f80,f79])).
% 1.69/0.59  fof(f80,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f52,f39])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f43,f36])).
% 1.69/0.59  fof(f36,plain,(
% 1.69/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(flattening,[],[f23])).
% 1.69/0.59  fof(f23,plain,(
% 1.69/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f7])).
% 1.69/0.59  fof(f7,axiom,(
% 1.69/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.69/0.59  fof(f179,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f178,f79])).
% 1.69/0.59  fof(f178,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f145,f79])).
% 1.69/0.59  fof(f145,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f43,f43,f43,f32])).
% 1.69/0.59  fof(f32,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f20])).
% 1.69/0.59  fof(f20,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f11])).
% 1.69/0.59  fof(f11,axiom,(
% 1.69/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.69/0.59  fof(f90,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.69/0.59    inference(backward_demodulation,[],[f58,f79])).
% 1.69/0.59  fof(f58,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f52,f37])).
% 1.69/0.59  % SZS output end Proof for theBenchmark
% 1.69/0.59  % (12504)------------------------------
% 1.69/0.59  % (12504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (12504)Termination reason: Refutation
% 1.69/0.59  
% 1.69/0.59  % (12504)Memory used [KB]: 2174
% 1.69/0.59  % (12504)Time elapsed: 0.185 s
% 1.69/0.59  % (12504)------------------------------
% 1.69/0.59  % (12504)------------------------------
% 1.69/0.59  % (12481)Success in time 0.218 s
%------------------------------------------------------------------------------
