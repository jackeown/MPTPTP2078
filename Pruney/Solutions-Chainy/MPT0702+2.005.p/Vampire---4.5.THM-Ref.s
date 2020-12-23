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
% DateTime   : Thu Dec  3 12:54:12 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 207 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 983 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(subsumption_resolution,[],[f412,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f412,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f176,f137])).

fof(f137,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f136,f92])).

fof(f92,plain,(
    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f90,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f54,f28])).

fof(f28,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f136,plain,(
    k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f135,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f135,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f133,f92])).

fof(f133,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k10_relat_1(sK2,k9_relat_1(sK2,sK0)))
    | k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f62,f69])).

fof(f69,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f57,f40])).

fof(f176,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f31,f77])).

fof(f77,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (29415)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (29437)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (29429)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (29423)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (29421)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (29431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.71/0.58  % (29416)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.71/0.58  % (29426)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.71/0.59  % (29421)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % (29430)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.71/0.60  % (29414)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.71/0.60  % (29425)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.71/0.60  % (29428)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.71/0.60  % (29420)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.60  % (29419)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.71/0.60  % (29417)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.71/0.60  % (29432)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.89/0.60  % (29443)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.89/0.60  % (29443)Refutation not found, incomplete strategy% (29443)------------------------------
% 1.89/0.60  % (29443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.60  % (29443)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.60  
% 1.89/0.60  % (29443)Memory used [KB]: 1663
% 1.89/0.60  % (29443)Time elapsed: 0.001 s
% 1.89/0.60  % (29443)------------------------------
% 1.89/0.60  % (29443)------------------------------
% 1.89/0.60  % (29442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.89/0.61  % (29422)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.89/0.61  % (29418)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.89/0.61  % (29424)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.89/0.61  % (29438)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.89/0.61  % (29436)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.89/0.61  % (29430)Refutation not found, incomplete strategy% (29430)------------------------------
% 1.89/0.61  % (29430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % SZS output start Proof for theBenchmark
% 1.89/0.61  fof(f414,plain,(
% 1.89/0.61    $false),
% 1.89/0.61    inference(subsumption_resolution,[],[f412,f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ~r1_tarski(sK0,sK1)),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f22,plain,(
% 1.89/0.61    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.89/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 1.89/0.61  fof(f21,plain,(
% 1.89/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f13,plain,(
% 1.89/0.61    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.89/0.61    inference(flattening,[],[f12])).
% 1.89/0.61  fof(f12,plain,(
% 1.89/0.61    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.89/0.61    inference(ennf_transformation,[],[f11])).
% 1.89/0.61  fof(f11,negated_conjecture,(
% 1.89/0.61    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.89/0.61    inference(negated_conjecture,[],[f10])).
% 1.89/0.61  fof(f10,conjecture,(
% 1.89/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.89/0.61  fof(f412,plain,(
% 1.89/0.61    r1_tarski(sK0,sK1)),
% 1.89/0.61    inference(superposition,[],[f176,f137])).
% 1.89/0.61  fof(f137,plain,(
% 1.89/0.61    sK0 = k3_xboole_0(sK0,sK1)),
% 1.89/0.61    inference(forward_demodulation,[],[f136,f92])).
% 1.89/0.61  fof(f92,plain,(
% 1.89/0.61    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(subsumption_resolution,[],[f90,f57])).
% 1.89/0.61  fof(f57,plain,(
% 1.89/0.61    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f56,f25])).
% 1.89/0.61  fof(f25,plain,(
% 1.89/0.61    v1_relat_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f56,plain,(
% 1.89/0.61    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f55,f26])).
% 1.89/0.61  fof(f26,plain,(
% 1.89/0.61    v1_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f55,plain,(
% 1.89/0.61    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.89/0.61    inference(resolution,[],[f37,f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    v2_funct_1(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f37,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f18])).
% 1.89/0.61  fof(f18,plain,(
% 1.89/0.61    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f17])).
% 1.89/0.61  fof(f17,plain,(
% 1.89/0.61    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.89/0.61    inference(ennf_transformation,[],[f9])).
% 1.89/0.61  fof(f9,axiom,(
% 1.89/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.89/0.61  fof(f90,plain,(
% 1.89/0.61    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 1.89/0.61    inference(resolution,[],[f68,f40])).
% 1.89/0.61  fof(f40,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f24])).
% 1.89/0.61  fof(f24,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(flattening,[],[f23])).
% 1.89/0.61  fof(f23,plain,(
% 1.89/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.61    inference(nnf_transformation,[],[f1])).
% 1.89/0.61  fof(f1,axiom,(
% 1.89/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.61  fof(f68,plain,(
% 1.89/0.61    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 1.89/0.61    inference(resolution,[],[f54,f28])).
% 1.89/0.61  fof(f28,plain,(
% 1.89/0.61    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) )),
% 1.89/0.61    inference(resolution,[],[f35,f25])).
% 1.89/0.61  fof(f35,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f15])).
% 1.89/0.61  fof(f15,plain,(
% 1.89/0.61    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(flattening,[],[f14])).
% 1.89/0.61  fof(f14,plain,(
% 1.89/0.61    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f8])).
% 1.89/0.61  fof(f8,axiom,(
% 1.89/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.89/0.61  fof(f136,plain,(
% 1.89/0.61    k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(subsumption_resolution,[],[f135,f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f2])).
% 1.89/0.61  fof(f2,axiom,(
% 1.89/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.89/0.61  fof(f135,plain,(
% 1.89/0.61    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(forward_demodulation,[],[f133,f92])).
% 1.89/0.61  fof(f133,plain,(
% 1.89/0.61    ~r1_tarski(k3_xboole_0(sK0,sK1),k10_relat_1(sK2,k9_relat_1(sK2,sK0))) | k3_xboole_0(sK0,sK1) = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.89/0.61    inference(superposition,[],[f62,f69])).
% 1.89/0.61  fof(f69,plain,(
% 1.89/0.61    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 1.89/0.61    inference(superposition,[],[f60,f48])).
% 1.89/0.61  fof(f48,plain,(
% 1.89/0.61    k9_relat_1(sK2,sK0) = k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.89/0.61    inference(resolution,[],[f36,f27])).
% 1.89/0.61  fof(f27,plain,(
% 1.89/0.61    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.89/0.61    inference(cnf_transformation,[],[f22])).
% 1.89/0.61  fof(f36,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.89/0.61    inference(cnf_transformation,[],[f16])).
% 1.89/0.61  fof(f16,plain,(
% 1.89/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.89/0.61    inference(ennf_transformation,[],[f3])).
% 1.89/0.61  fof(f3,axiom,(
% 1.89/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.89/0.61  fof(f60,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f59,f25])).
% 1.89/0.61  fof(f59,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f58,f26])).
% 1.89/0.61  fof(f58,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.89/0.61    inference(resolution,[],[f41,f29])).
% 1.89/0.61  fof(f41,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f20])).
% 1.89/0.61  fof(f20,plain,(
% 1.89/0.61    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.89/0.61    inference(flattening,[],[f19])).
% 1.89/0.61  fof(f19,plain,(
% 1.89/0.61    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.89/0.61    inference(ennf_transformation,[],[f7])).
% 1.89/0.61  fof(f7,axiom,(
% 1.89/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) )),
% 1.89/0.61    inference(resolution,[],[f57,f40])).
% 1.89/0.61  fof(f176,plain,(
% 1.89/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.89/0.61    inference(superposition,[],[f31,f77])).
% 1.89/0.61  fof(f77,plain,(
% 1.89/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.89/0.61    inference(superposition,[],[f44,f33])).
% 1.89/0.61  fof(f33,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.89/0.61    inference(cnf_transformation,[],[f6])).
% 1.89/0.61  fof(f6,axiom,(
% 1.89/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.89/0.61  fof(f44,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.89/0.61    inference(superposition,[],[f33,f32])).
% 1.89/0.61  fof(f32,plain,(
% 1.89/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f4])).
% 1.89/0.61  fof(f4,axiom,(
% 1.89/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.89/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.89/0.61  % SZS output end Proof for theBenchmark
% 1.89/0.61  % (29421)------------------------------
% 1.89/0.61  % (29421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.61  % (29421)Termination reason: Refutation
% 1.89/0.61  
% 1.89/0.61  % (29421)Memory used [KB]: 1918
% 1.89/0.61  % (29421)Time elapsed: 0.105 s
% 1.89/0.61  % (29421)------------------------------
% 1.89/0.61  % (29421)------------------------------
% 1.89/0.61  % (29434)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.89/0.61  % (29440)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.89/0.61  % (29439)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.89/0.61  % (29430)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.61  
% 1.89/0.61  % (29430)Memory used [KB]: 10618
% 1.89/0.61  % (29430)Time elapsed: 0.182 s
% 1.89/0.61  % (29430)------------------------------
% 1.89/0.61  % (29430)------------------------------
% 1.89/0.61  % (29413)Success in time 0.245 s
%------------------------------------------------------------------------------
