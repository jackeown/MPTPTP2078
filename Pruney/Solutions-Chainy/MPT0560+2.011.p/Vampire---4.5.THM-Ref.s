%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:01 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 127 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 268 expanded)
%              Number of equality atoms :   59 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f934,plain,(
    $false ),
    inference(subsumption_resolution,[],[f933,f34])).

fof(f34,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f933,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(superposition,[],[f155,f903])).

fof(f903,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f874,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f874,plain,(
    k2_relat_1(k6_relat_1(sK1)) = k9_relat_1(k6_relat_1(sK2),sK1) ),
    inference(superposition,[],[f78,f851])).

fof(f851,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK2),sK1) ),
    inference(resolution,[],[f845,f102])).

fof(f102,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k6_relat_1(X3),k7_relat_1(k6_relat_1(X4),X3))
      | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3) ) ),
    inference(forward_demodulation,[],[f101,f75])).

fof(f75,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f101,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3)
      | ~ r1_tarski(k6_relat_1(X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) ) ),
    inference(forward_demodulation,[],[f99,f75])).

fof(f99,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))
      | ~ r1_tarski(k6_relat_1(X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f58,plain,(
    ! [X2,X1] : r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f845,plain,(
    r1_tarski(k6_relat_1(sK1),k7_relat_1(k6_relat_1(sK2),sK1)) ),
    inference(superposition,[],[f827,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f54,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f38,f35])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f827,plain,(
    ! [X10] : r1_tarski(k7_relat_1(k6_relat_1(sK1),X10),k7_relat_1(k6_relat_1(sK2),X10)) ),
    inference(superposition,[],[f390,f128])).

fof(f128,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    inference(resolution,[],[f85,f33])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f390,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f385,f35])).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f59,f200])).

fof(f200,plain,(
    ! [X4,X2,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X2),X4),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4) ),
    inference(forward_demodulation,[],[f198,f75])).

fof(f198,plain,(
    ! [X4,X2,X3] : k7_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X4),k6_relat_1(X3)) ),
    inference(resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(X2,X4),k6_relat_1(X3)) ) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k5_relat_1(k7_relat_1(X3,X4),k6_relat_1(X5)),k7_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f78,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f155,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k7_relat_1(sK0,X1),X2) ),
    inference(forward_demodulation,[],[f153,f74])).

fof(f74,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f153,plain,(
    ! [X2,X1] : k9_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f87,f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,sK0),X1) = k9_relat_1(sK0,k9_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:39:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (5339)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (5330)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (5327)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5338)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (5351)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.42/0.55  % (5340)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (5343)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.42/0.55  % (5334)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.42/0.56  % (5335)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.42/0.56  % (5326)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.60/0.56  % (5331)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.60/0.57  % (5342)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.60/0.57  % (5329)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.60/0.57  % (5348)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.60/0.58  % (5341)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.58  % (5349)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.60/0.58  % (5347)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.58  % (5332)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.60/0.60  % (5328)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.60/0.61  % (5353)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.60/0.61  % (5345)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.60/0.62  % (5337)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 2.07/0.63  % (5343)Refutation found. Thanks to Tanya!
% 2.07/0.63  % SZS status Theorem for theBenchmark
% 2.07/0.63  % SZS output start Proof for theBenchmark
% 2.07/0.63  fof(f934,plain,(
% 2.07/0.63    $false),
% 2.07/0.63    inference(subsumption_resolution,[],[f933,f34])).
% 2.07/0.63  fof(f34,plain,(
% 2.07/0.63    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f29,plain,(
% 2.07/0.63    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 2.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27])).
% 2.07/0.63  fof(f27,plain,(
% 2.07/0.63    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f28,plain,(
% 2.07/0.63    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 2.07/0.63    introduced(choice_axiom,[])).
% 2.07/0.63  fof(f15,plain,(
% 2.07/0.63    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f14])).
% 2.07/0.63  fof(f14,negated_conjecture,(
% 2.07/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.07/0.63    inference(negated_conjecture,[],[f13])).
% 2.07/0.63  fof(f13,conjecture,(
% 2.07/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 2.07/0.63  fof(f933,plain,(
% 2.07/0.63    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 2.07/0.63    inference(superposition,[],[f155,f903])).
% 2.07/0.63  fof(f903,plain,(
% 2.07/0.63    sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 2.07/0.63    inference(forward_demodulation,[],[f874,f37])).
% 2.07/0.63  fof(f37,plain,(
% 2.07/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.07/0.63    inference(cnf_transformation,[],[f8])).
% 2.07/0.63  fof(f8,axiom,(
% 2.07/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.07/0.63  fof(f874,plain,(
% 2.07/0.63    k2_relat_1(k6_relat_1(sK1)) = k9_relat_1(k6_relat_1(sK2),sK1)),
% 2.07/0.63    inference(superposition,[],[f78,f851])).
% 2.07/0.63  fof(f851,plain,(
% 2.07/0.63    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK2),sK1)),
% 2.07/0.63    inference(resolution,[],[f845,f102])).
% 2.07/0.63  fof(f102,plain,(
% 2.07/0.63    ( ! [X4,X3] : (~r1_tarski(k6_relat_1(X3),k7_relat_1(k6_relat_1(X4),X3)) | k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3)) )),
% 2.07/0.63    inference(forward_demodulation,[],[f101,f75])).
% 2.07/0.63  fof(f75,plain,(
% 2.07/0.63    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 2.07/0.63    inference(resolution,[],[f40,f35])).
% 2.07/0.63  fof(f35,plain,(
% 2.07/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.07/0.63    inference(cnf_transformation,[],[f3])).
% 2.07/0.63  fof(f3,axiom,(
% 2.07/0.63    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.07/0.63  fof(f40,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f18])).
% 2.07/0.63  fof(f18,plain,(
% 2.07/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f10])).
% 2.07/0.63  fof(f10,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.07/0.63  fof(f101,plain,(
% 2.07/0.63    ( ! [X4,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3) | ~r1_tarski(k6_relat_1(X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)))) )),
% 2.07/0.63    inference(forward_demodulation,[],[f99,f75])).
% 2.07/0.63  fof(f99,plain,(
% 2.07/0.63    ( ! [X4,X3] : (k6_relat_1(X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)) | ~r1_tarski(k6_relat_1(X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)))) )),
% 2.07/0.63    inference(resolution,[],[f58,f49])).
% 2.07/0.63  fof(f49,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f31])).
% 2.07/0.63  fof(f31,plain,(
% 2.07/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.63    inference(flattening,[],[f30])).
% 2.07/0.63  fof(f30,plain,(
% 2.07/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.63    inference(nnf_transformation,[],[f1])).
% 2.07/0.63  fof(f1,axiom,(
% 2.07/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.07/0.63  fof(f58,plain,(
% 2.07/0.63    ( ! [X2,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))) )),
% 2.07/0.63    inference(resolution,[],[f42,f35])).
% 2.07/0.63  fof(f42,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f20])).
% 2.07/0.63  fof(f20,plain,(
% 2.07/0.63    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f9])).
% 2.07/0.63  fof(f9,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 2.07/0.63  fof(f845,plain,(
% 2.07/0.63    r1_tarski(k6_relat_1(sK1),k7_relat_1(k6_relat_1(sK2),sK1))),
% 2.07/0.63    inference(superposition,[],[f827,f56])).
% 2.07/0.63  fof(f56,plain,(
% 2.07/0.63    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.07/0.63    inference(forward_demodulation,[],[f54,f36])).
% 2.07/0.63  fof(f36,plain,(
% 2.07/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.07/0.63    inference(cnf_transformation,[],[f8])).
% 2.07/0.63  fof(f54,plain,(
% 2.07/0.63    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.07/0.63    inference(resolution,[],[f38,f35])).
% 2.07/0.63  fof(f38,plain,(
% 2.07/0.63    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f16,plain,(
% 2.07/0.63    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f12])).
% 2.07/0.63  fof(f12,axiom,(
% 2.07/0.63    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 2.07/0.63  fof(f827,plain,(
% 2.07/0.63    ( ! [X10] : (r1_tarski(k7_relat_1(k6_relat_1(sK1),X10),k7_relat_1(k6_relat_1(sK2),X10))) )),
% 2.07/0.63    inference(superposition,[],[f390,f128])).
% 2.07/0.63  fof(f128,plain,(
% 2.07/0.63    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 2.07/0.63    inference(resolution,[],[f85,f33])).
% 2.07/0.63  fof(f33,plain,(
% 2.07/0.63    r1_tarski(sK1,sK2)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f85,plain,(
% 2.07/0.63    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 2.07/0.63    inference(forward_demodulation,[],[f83,f36])).
% 2.07/0.63  fof(f83,plain,(
% 2.07/0.63    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 2.07/0.63    inference(resolution,[],[f44,f35])).
% 2.07/0.63  fof(f44,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 2.07/0.63    inference(cnf_transformation,[],[f22])).
% 2.07/0.63  fof(f22,plain,(
% 2.07/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(flattening,[],[f21])).
% 2.07/0.63  fof(f21,plain,(
% 2.07/0.63    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f11])).
% 2.07/0.63  fof(f11,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.07/0.63  fof(f390,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.07/0.63    inference(subsumption_resolution,[],[f385,f35])).
% 2.07/0.63  fof(f385,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.07/0.63    inference(superposition,[],[f59,f200])).
% 2.07/0.63  fof(f200,plain,(
% 2.07/0.63    ( ! [X4,X2,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X2),X4),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X4)) )),
% 2.07/0.63    inference(forward_demodulation,[],[f198,f75])).
% 2.07/0.63  fof(f198,plain,(
% 2.07/0.63    ( ! [X4,X2,X3] : (k7_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X2),X4),k6_relat_1(X3))) )),
% 2.07/0.63    inference(resolution,[],[f92,f35])).
% 2.07/0.63  fof(f92,plain,(
% 2.07/0.63    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k7_relat_1(X2,X4),k6_relat_1(X3))) )),
% 2.07/0.63    inference(resolution,[],[f46,f35])).
% 2.07/0.63  fof(f46,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f24])).
% 2.07/0.63  fof(f24,plain,(
% 2.07/0.63    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f5])).
% 2.07/0.63  fof(f5,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 2.07/0.63  fof(f59,plain,(
% 2.07/0.63    ( ! [X4,X5,X3] : (r1_tarski(k5_relat_1(k7_relat_1(X3,X4),k6_relat_1(X5)),k7_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 2.07/0.63    inference(resolution,[],[f42,f39])).
% 2.07/0.63  fof(f39,plain,(
% 2.07/0.63    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f17])).
% 2.07/0.63  fof(f17,plain,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f4])).
% 2.07/0.63  fof(f4,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.07/0.63  fof(f78,plain,(
% 2.07/0.63    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 2.07/0.63    inference(resolution,[],[f41,f35])).
% 2.07/0.63  fof(f41,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f19])).
% 2.07/0.63  fof(f19,plain,(
% 2.07/0.63    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f6])).
% 2.07/0.63  fof(f6,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.07/0.63  fof(f155,plain,(
% 2.07/0.63    ( ! [X2,X1] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k7_relat_1(sK0,X1),X2)) )),
% 2.07/0.63    inference(forward_demodulation,[],[f153,f74])).
% 2.07/0.63  fof(f74,plain,(
% 2.07/0.63    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)) )),
% 2.07/0.63    inference(resolution,[],[f40,f32])).
% 2.07/0.63  fof(f32,plain,(
% 2.07/0.63    v1_relat_1(sK0)),
% 2.07/0.63    inference(cnf_transformation,[],[f29])).
% 2.07/0.63  fof(f153,plain,(
% 2.07/0.63    ( ! [X2,X1] : (k9_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X2))) )),
% 2.07/0.63    inference(resolution,[],[f87,f35])).
% 2.07/0.63  fof(f87,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,sK0),X1) = k9_relat_1(sK0,k9_relat_1(X0,X1))) )),
% 2.07/0.63    inference(resolution,[],[f45,f32])).
% 2.07/0.63  fof(f45,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f23])).
% 2.07/0.63  fof(f23,plain,(
% 2.07/0.63    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f7])).
% 2.07/0.63  fof(f7,axiom,(
% 2.07/0.63    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 2.07/0.63  % SZS output end Proof for theBenchmark
% 2.07/0.63  % (5343)------------------------------
% 2.07/0.63  % (5343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (5343)Termination reason: Refutation
% 2.07/0.63  
% 2.07/0.63  % (5343)Memory used [KB]: 2302
% 2.07/0.63  % (5343)Time elapsed: 0.204 s
% 2.07/0.63  % (5343)------------------------------
% 2.07/0.63  % (5343)------------------------------
% 2.07/0.63  % (5325)Success in time 0.27 s
%------------------------------------------------------------------------------
