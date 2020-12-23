%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 125 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   21
%              Number of atoms          :  152 ( 326 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f533,plain,(
    $false ),
    inference(subsumption_resolution,[],[f532,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f532,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f531,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f531,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f529,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f529,plain,(
    ! [X1] : ~ r1_tarski(sK0,k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f527,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f527,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,sK0)
      | ~ r1_tarski(sK0,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f492,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f492,plain,(
    ! [X8] : ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8))) ),
    inference(subsumption_resolution,[],[f490,f32])).

fof(f490,plain,(
    ! [X8] :
      ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f483,f182])).

fof(f182,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f177,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f177,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(k7_relat_1(X8,X9))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f483,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f481,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f481,plain,(
    ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f478,f49])).

fof(f478,plain,(
    ! [X2] :
      ( ~ r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0))
      | ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(subsumption_resolution,[],[f476,f32])).

fof(f476,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2)))
      | ~ r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f470,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f116,f38])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f470,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0))
      | ~ r1_tarski(X0,k9_relat_1(sK1,sK0)) ) ),
    inference(subsumption_resolution,[],[f449,f32])).

fof(f449,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k9_relat_1(sK1,sK0))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0)) ) ),
    inference(resolution,[],[f180,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f103,f48])).

fof(f103,plain,(
    ! [X3] : ~ r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f95,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2)))
      | ~ r1_tarski(X3,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f175,f38])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2)))
      | ~ r1_tarski(X3,X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f45])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (18715)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.45  % (18703)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.46  % (18707)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.47  % (18716)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (18705)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.47  % (18725)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.48  % (18704)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.48  % (18708)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.48  % (18726)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.49  % (18720)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.49  % (18707)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (18728)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.49  % (18718)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.49  % (18712)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.49  % (18722)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f533,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f532,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    v1_relat_1(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.19/0.49    inference(flattening,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.49    inference(negated_conjecture,[],[f13])).
% 0.19/0.49  fof(f13,conjecture,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.19/0.49  fof(f532,plain,(
% 0.19/0.49    ~v1_relat_1(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f531,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f531,plain,(
% 0.19/0.49    ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.49    inference(superposition,[],[f529,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.49  fof(f529,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(sK0,k10_relat_1(sK1,X1))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f527,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f43])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(flattening,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.49  fof(f527,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(sK0,sK0) | ~r1_tarski(sK0,k10_relat_1(sK1,X1))) )),
% 0.19/0.49    inference(superposition,[],[f492,f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.49  fof(f492,plain,(
% 0.19/0.49    ( ! [X8] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8)))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f490,f32])).
% 0.19/0.49  fof(f490,plain,(
% 0.19/0.49    ( ! [X8] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X8))) | ~v1_relat_1(sK1)) )),
% 0.19/0.49    inference(resolution,[],[f483,f182])).
% 0.19/0.49  fof(f182,plain,(
% 0.19/0.49    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(X8)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f177,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.19/0.49  fof(f177,plain,(
% 0.19/0.49    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(k7_relat_1(X8,X9)) | ~v1_relat_1(X8)) )),
% 0.19/0.49    inference(superposition,[],[f39,f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.19/0.49  fof(f483,plain,(
% 0.19/0.49    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f481,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.49  fof(f481,plain,(
% 0.19/0.49    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.19/0.49    inference(resolution,[],[f478,f49])).
% 0.19/0.49  fof(f478,plain,(
% 0.19/0.49    ( ! [X2] : (~r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0)) | ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f476,f32])).
% 0.19/0.49  fof(f476,plain,(
% 0.19/0.49    ( ! [X2] : (~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,X2))) | ~r1_tarski(k9_relat_1(sK1,X2),k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)) )),
% 0.19/0.49    inference(superposition,[],[f470,f117])).
% 0.19/0.49  fof(f117,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f116,f38])).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(superposition,[],[f35,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.49  fof(f470,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0)) | ~r1_tarski(X0,k9_relat_1(sK1,sK0))) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f449,f32])).
% 0.19/0.49  fof(f449,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,X1),X0))) )),
% 0.19/0.49    inference(resolution,[],[f180,f111])).
% 0.19/0.49  fof(f111,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) | ~r1_tarski(sK0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f103,f48])).
% 0.19/0.49  fof(f103,plain,(
% 0.19/0.49    ( ! [X3] : (~r1_tarski(sK0,k3_xboole_0(X3,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 0.19/0.49    inference(resolution,[],[f95,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.19/0.49    inference(superposition,[],[f36,f37])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X0)) )),
% 0.19/0.49    inference(resolution,[],[f48,f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f180,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2))) | ~r1_tarski(X3,X2) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f175,f38])).
% 0.19/0.49  fof(f175,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k10_relat_1(k7_relat_1(X0,X1),X3),k3_xboole_0(X1,k10_relat_1(X0,X2))) | ~r1_tarski(X3,X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(superposition,[],[f46,f45])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (18707)------------------------------
% 0.19/0.49  % (18707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (18707)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (18707)Memory used [KB]: 6396
% 0.19/0.49  % (18707)Time elapsed: 0.102 s
% 0.19/0.49  % (18707)------------------------------
% 0.19/0.49  % (18707)------------------------------
% 0.19/0.49  % (18719)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.49  % (18702)Success in time 0.151 s
%------------------------------------------------------------------------------
