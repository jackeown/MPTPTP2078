%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:59 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 143 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  133 ( 282 expanded)
%              Number of equality atoms :   67 ( 126 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f859,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f858])).

fof(f858,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(backward_demodulation,[],[f92,f857])).

fof(f857,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f841,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f841,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f48,f795])).

fof(f795,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f794,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f64,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f48,f40])).

fof(f794,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f784,f127])).

fof(f127,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),k4_xboole_0(X4,X5))) ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f76,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X2)))
      | k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) = X1 ) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f784,plain,(
    k4_xboole_0(sK0,sK1) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k4_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f127,f310])).

fof(f310,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK1)) = k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK0)) ),
    inference(backward_demodulation,[],[f150,f306])).

fof(f306,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) ),
    inference(superposition,[],[f85,f119])).

fof(f119,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f85,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X2),X4)) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X3,X4)) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f61,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f57,f45])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(f150,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK1)) = k4_xboole_0(k7_relat_1(k6_relat_1(sK0),X0),k6_relat_1(sK0)) ),
    inference(superposition,[],[f85,f123])).

fof(f123,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(resolution,[],[f74,f36])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f92,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f80,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(f80,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f37,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (9901)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.48  % (9918)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (9918)Refutation not found, incomplete strategy% (9918)------------------------------
% 0.19/0.49  % (9918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (9918)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (9918)Memory used [KB]: 1663
% 0.19/0.49  % (9918)Time elapsed: 0.085 s
% 0.19/0.49  % (9918)------------------------------
% 0.19/0.49  % (9918)------------------------------
% 0.19/0.50  % (9892)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (9893)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (9910)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.51  % (9895)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (9909)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.28/0.52  % (9889)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.52  % (9894)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.52  % (9916)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.52  % (9912)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.52  % (9911)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.52  % (9900)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.53  % (9891)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.53  % (9903)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.53  % (9890)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.53  % (9905)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.53  % (9915)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.53  % (9888)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.53  % (9902)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.53  % (9913)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.54  % (9908)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.54  % (9898)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.54  % (9917)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.54  % (9899)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.54  % (9904)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.54  % (9897)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.54  % (9917)Refutation not found, incomplete strategy% (9917)------------------------------
% 1.43/0.54  % (9917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (9917)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (9917)Memory used [KB]: 10746
% 1.43/0.54  % (9917)Time elapsed: 0.143 s
% 1.43/0.54  % (9917)------------------------------
% 1.43/0.54  % (9917)------------------------------
% 1.43/0.54  % (9896)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.55  % (9904)Refutation not found, incomplete strategy% (9904)------------------------------
% 1.43/0.55  % (9904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (9904)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (9904)Memory used [KB]: 10618
% 1.43/0.55  % (9904)Time elapsed: 0.150 s
% 1.43/0.55  % (9904)------------------------------
% 1.43/0.55  % (9904)------------------------------
% 1.43/0.55  % (9907)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.55  % (9914)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.56  % (9898)Refutation not found, incomplete strategy% (9898)------------------------------
% 1.43/0.56  % (9898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (9898)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (9898)Memory used [KB]: 10746
% 1.43/0.56  % (9898)Time elapsed: 0.156 s
% 1.43/0.56  % (9898)------------------------------
% 1.43/0.56  % (9898)------------------------------
% 1.43/0.56  % (9895)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f859,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f858])).
% 1.43/0.56  fof(f858,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)),
% 1.43/0.56    inference(backward_demodulation,[],[f92,f857])).
% 1.43/0.56  fof(f857,plain,(
% 1.43/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.43/0.56    inference(forward_demodulation,[],[f841,f40])).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.43/0.56  fof(f841,plain,(
% 1.43/0.56    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.43/0.56    inference(superposition,[],[f48,f795])).
% 1.43/0.56  fof(f795,plain,(
% 1.43/0.56    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.43/0.56    inference(forward_demodulation,[],[f794,f67])).
% 1.43/0.56  fof(f67,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f64,f39])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.43/0.56    inference(superposition,[],[f48,f40])).
% 1.43/0.56  fof(f794,plain,(
% 1.43/0.56    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)),
% 1.43/0.56    inference(forward_demodulation,[],[f784,f127])).
% 1.43/0.56  fof(f127,plain,(
% 1.43/0.56    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),k4_xboole_0(X4,X5)))) )),
% 1.43/0.56    inference(resolution,[],[f77,f44])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.43/0.56  fof(f77,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) = X1) )),
% 1.43/0.56    inference(forward_demodulation,[],[f76,f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,axiom,(
% 1.43/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.43/0.56  fof(f76,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(k6_relat_1(X2))) | k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) = X1) )),
% 1.43/0.56    inference(resolution,[],[f49,f41])).
% 1.43/0.56  fof(f41,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.43/0.56    inference(pure_predicate_removal,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.43/0.56  fof(f784,plain,(
% 1.43/0.56    k4_xboole_0(sK0,sK1) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k4_xboole_0(sK0,sK0)))),
% 1.43/0.56    inference(superposition,[],[f127,f310])).
% 1.43/0.56  fof(f310,plain,(
% 1.43/0.56    ( ! [X0] : (k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK1)) = k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK0))) )),
% 1.43/0.56    inference(backward_demodulation,[],[f150,f306])).
% 1.43/0.56  fof(f306,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0))) )),
% 1.43/0.56    inference(superposition,[],[f85,f119])).
% 1.43/0.56  fof(f119,plain,(
% 1.43/0.56    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.43/0.56    inference(resolution,[],[f74,f59])).
% 1.43/0.56  fof(f59,plain,(
% 1.43/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.56    inference(equality_resolution,[],[f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f34])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.56    inference(flattening,[],[f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f73,f42])).
% 1.43/0.56  fof(f73,plain,(
% 1.43/0.56    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.43/0.56    inference(resolution,[],[f50,f41])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.43/0.56    inference(cnf_transformation,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.43/0.56  fof(f85,plain,(
% 1.43/0.56    ( ! [X4,X2,X3] : (k4_xboole_0(k7_relat_1(k6_relat_1(X2),X3),k7_relat_1(k6_relat_1(X2),X4)) = k7_relat_1(k6_relat_1(X2),k4_xboole_0(X3,X4))) )),
% 1.43/0.56    inference(resolution,[],[f62,f41])).
% 1.43/0.56  fof(f62,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f61,f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.43/0.56  fof(f61,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f57,f45])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).
% 1.43/0.56  fof(f150,plain,(
% 1.43/0.56    ( ! [X0] : (k7_relat_1(k6_relat_1(sK0),k4_xboole_0(X0,sK1)) = k4_xboole_0(k7_relat_1(k6_relat_1(sK0),X0),k6_relat_1(sK0))) )),
% 1.43/0.56    inference(superposition,[],[f85,f123])).
% 1.43/0.56  fof(f123,plain,(
% 1.43/0.56    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.43/0.56    inference(resolution,[],[f74,f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    r1_tarski(sK0,sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.43/0.56    inference(flattening,[],[f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.43/0.56    inference(negated_conjecture,[],[f19])).
% 1.43/0.56  fof(f19,conjecture,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 1.43/0.56    inference(superposition,[],[f37,f82])).
% 1.43/0.56  fof(f82,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X1,X0))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f80,f78])).
% 1.43/0.56  fof(f78,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(resolution,[],[f55,f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    v1_relat_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f32])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) )),
% 1.43/0.56    inference(resolution,[],[f56,f35])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.43/0.56    inference(ennf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f32])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (9895)------------------------------
% 1.43/0.56  % (9895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (9895)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (9895)Memory used [KB]: 2558
% 1.43/0.56  % (9895)Time elapsed: 0.161 s
% 1.43/0.56  % (9895)------------------------------
% 1.43/0.56  % (9895)------------------------------
% 1.43/0.59  % (9887)Success in time 0.231 s
%------------------------------------------------------------------------------
