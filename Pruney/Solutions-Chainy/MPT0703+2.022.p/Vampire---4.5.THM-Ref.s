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
% DateTime   : Thu Dec  3 12:54:21 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 138 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 516 expanded)
%              Number of equality atoms :   44 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1371,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f32,f1225,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1225,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1202,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f91,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f44,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f38,f47])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1202,plain,(
    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f36,f1098])).

fof(f1098,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1096,f84])).

fof(f84,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1096,plain,(
    k3_xboole_0(sK0,sK1) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f300,f85])).

fof(f85,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f70,f55])).

fof(f55,plain,(
    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f69,f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f46,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f300,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0))) ),
    inference(resolution,[],[f276,f68])).

fof(f276,plain,(
    ! [X16] : r1_tarski(k3_xboole_0(sK0,X16),k2_relat_1(sK2)) ),
    inference(resolution,[],[f110,f31])).

fof(f110,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | r1_tarski(k3_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f32,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (12121)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.48  % (12137)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.49  % (12113)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.49  % (12122)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (12116)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (12112)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (12133)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (12125)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (12138)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (12111)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (12114)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (12138)Refutation not found, incomplete strategy% (12138)------------------------------
% 0.20/0.51  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12115)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (12132)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (12117)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (12118)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (12110)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (12120)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (12138)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12138)Memory used [KB]: 10746
% 0.20/0.52  % (12138)Time elapsed: 0.106 s
% 0.20/0.52  % (12138)------------------------------
% 0.20/0.52  % (12138)------------------------------
% 0.20/0.52  % (12123)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.52  % (12130)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.53  % (12139)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.53  % (12135)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.53  % (12126)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.53  % (12129)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.53  % (12124)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.53  % (12136)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (12127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (12128)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (12126)Refutation not found, incomplete strategy% (12126)------------------------------
% 1.34/0.54  % (12126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12126)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12126)Memory used [KB]: 10618
% 1.34/0.54  % (12126)Time elapsed: 0.140 s
% 1.34/0.54  % (12126)------------------------------
% 1.34/0.54  % (12126)------------------------------
% 1.34/0.54  % (12131)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.54  % (12134)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.55  % (12120)Refutation not found, incomplete strategy% (12120)------------------------------
% 1.47/0.55  % (12120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (12120)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (12120)Memory used [KB]: 10746
% 1.47/0.55  % (12120)Time elapsed: 0.155 s
% 1.47/0.55  % (12120)------------------------------
% 1.47/0.55  % (12120)------------------------------
% 1.47/0.55  % (12139)Refutation not found, incomplete strategy% (12139)------------------------------
% 1.47/0.55  % (12139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (12139)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (12139)Memory used [KB]: 1663
% 1.47/0.55  % (12139)Time elapsed: 0.003 s
% 1.47/0.55  % (12139)------------------------------
% 1.47/0.55  % (12139)------------------------------
% 1.47/0.55  % (12119)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.58  % (12117)Refutation found. Thanks to Tanya!
% 1.47/0.58  % SZS status Theorem for theBenchmark
% 1.47/0.59  % (12113)Refutation not found, incomplete strategy% (12113)------------------------------
% 1.47/0.59  % (12113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.59  % (12113)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.59  
% 1.47/0.59  % (12113)Memory used [KB]: 6140
% 1.47/0.59  % (12113)Time elapsed: 0.189 s
% 1.47/0.59  % (12113)------------------------------
% 1.47/0.59  % (12113)------------------------------
% 1.47/0.60  % SZS output start Proof for theBenchmark
% 1.47/0.60  fof(f1371,plain,(
% 1.47/0.60    $false),
% 1.47/0.60    inference(unit_resulting_resolution,[],[f32,f1225,f43])).
% 1.47/0.60  fof(f43,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f27])).
% 1.47/0.60  fof(f27,plain,(
% 1.47/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.47/0.60    inference(nnf_transformation,[],[f2])).
% 1.47/0.60  fof(f2,axiom,(
% 1.47/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.47/0.60  fof(f1225,plain,(
% 1.47/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.47/0.60    inference(forward_demodulation,[],[f1202,f94])).
% 1.47/0.60  fof(f94,plain,(
% 1.47/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.47/0.60    inference(forward_demodulation,[],[f91,f57])).
% 1.47/0.60  fof(f57,plain,(
% 1.47/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.47/0.60    inference(resolution,[],[f44,f47])).
% 1.47/0.60  fof(f47,plain,(
% 1.47/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.60    inference(equality_resolution,[],[f41])).
% 1.47/0.60  fof(f41,plain,(
% 1.47/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.60    inference(cnf_transformation,[],[f26])).
% 1.47/0.60  fof(f26,plain,(
% 1.47/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.60    inference(flattening,[],[f25])).
% 1.47/0.60  fof(f25,plain,(
% 1.47/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.60    inference(nnf_transformation,[],[f1])).
% 1.47/0.60  fof(f1,axiom,(
% 1.47/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.60  fof(f44,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.47/0.60    inference(cnf_transformation,[],[f27])).
% 1.47/0.60  fof(f91,plain,(
% 1.47/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.47/0.60    inference(superposition,[],[f36,f53])).
% 1.47/0.60  fof(f53,plain,(
% 1.47/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.47/0.60    inference(resolution,[],[f38,f47])).
% 1.47/0.60  fof(f38,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.60    inference(cnf_transformation,[],[f17])).
% 1.47/0.60  fof(f17,plain,(
% 1.47/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.60    inference(ennf_transformation,[],[f7])).
% 1.47/0.60  fof(f7,axiom,(
% 1.47/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.60  fof(f36,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.60    inference(cnf_transformation,[],[f3])).
% 1.47/0.60  fof(f3,axiom,(
% 1.47/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.60  fof(f1202,plain,(
% 1.47/0.60    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)),
% 1.47/0.60    inference(superposition,[],[f36,f1098])).
% 1.47/0.60  fof(f1098,plain,(
% 1.47/0.60    sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.60    inference(forward_demodulation,[],[f1096,f84])).
% 1.47/0.60  fof(f84,plain,(
% 1.47/0.60    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.47/0.60    inference(resolution,[],[f68,f31])).
% 1.47/0.60  fof(f31,plain,(
% 1.47/0.60    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.47/0.60    inference(cnf_transformation,[],[f24])).
% 1.47/0.60  fof(f24,plain,(
% 1.47/0.60    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.47/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 1.47/0.60  fof(f23,plain,(
% 1.47/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.47/0.60    introduced(choice_axiom,[])).
% 1.47/0.60  fof(f15,plain,(
% 1.47/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.47/0.60    inference(flattening,[],[f14])).
% 1.47/0.60  fof(f14,plain,(
% 1.47/0.60    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.47/0.60    inference(ennf_transformation,[],[f13])).
% 1.47/0.60  fof(f13,negated_conjecture,(
% 1.47/0.60    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.47/0.60    inference(negated_conjecture,[],[f12])).
% 1.47/0.60  fof(f12,conjecture,(
% 1.47/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 1.47/0.60  fof(f68,plain,(
% 1.47/0.60    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 1.47/0.60    inference(subsumption_resolution,[],[f67,f28])).
% 1.47/0.60  fof(f28,plain,(
% 1.47/0.60    v1_relat_1(sK2)),
% 1.47/0.60    inference(cnf_transformation,[],[f24])).
% 1.47/0.60  fof(f67,plain,(
% 1.47/0.60    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 1.47/0.60    inference(resolution,[],[f39,f29])).
% 1.47/0.60  fof(f29,plain,(
% 1.47/0.60    v1_funct_1(sK2)),
% 1.47/0.60    inference(cnf_transformation,[],[f24])).
% 1.47/0.60  fof(f39,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f19])).
% 1.47/0.60  fof(f19,plain,(
% 1.47/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.47/0.60    inference(flattening,[],[f18])).
% 1.47/0.60  fof(f18,plain,(
% 1.47/0.60    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.47/0.60    inference(ennf_transformation,[],[f11])).
% 1.47/0.60  fof(f11,axiom,(
% 1.47/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.47/0.60  fof(f1096,plain,(
% 1.47/0.60    k3_xboole_0(sK0,sK1) = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 1.47/0.60    inference(superposition,[],[f300,f85])).
% 1.47/0.60  fof(f85,plain,(
% 1.47/0.60    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 1.47/0.60    inference(superposition,[],[f70,f55])).
% 1.47/0.60  fof(f55,plain,(
% 1.47/0.60    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.47/0.60    inference(resolution,[],[f38,f30])).
% 1.47/0.60  fof(f30,plain,(
% 1.47/0.60    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.47/0.60    inference(cnf_transformation,[],[f24])).
% 1.47/0.60  fof(f70,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.47/0.60    inference(subsumption_resolution,[],[f69,f28])).
% 1.47/0.60  fof(f69,plain,(
% 1.47/0.60    ( ! [X0,X1] : (k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.47/0.60    inference(resolution,[],[f46,f29])).
% 1.47/0.60  fof(f46,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f22])).
% 1.47/0.60  fof(f22,plain,(
% 1.47/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.47/0.60    inference(flattening,[],[f21])).
% 1.47/0.60  fof(f21,plain,(
% 1.47/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.47/0.60    inference(ennf_transformation,[],[f10])).
% 1.47/0.60  fof(f10,axiom,(
% 1.47/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 1.47/0.60  fof(f300,plain,(
% 1.47/0.60    ( ! [X0] : (k3_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(sK0,X0)))) )),
% 1.47/0.60    inference(resolution,[],[f276,f68])).
% 1.47/0.60  fof(f276,plain,(
% 1.47/0.60    ( ! [X16] : (r1_tarski(k3_xboole_0(sK0,X16),k2_relat_1(sK2))) )),
% 1.47/0.60    inference(resolution,[],[f110,f31])).
% 1.47/0.60  fof(f110,plain,(
% 1.47/0.60    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | r1_tarski(k3_xboole_0(X2,X3),X4)) )),
% 1.47/0.60    inference(superposition,[],[f45,f50])).
% 1.47/0.60  fof(f50,plain,(
% 1.47/0.60    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 1.47/0.60    inference(resolution,[],[f37,f33])).
% 1.47/0.60  fof(f33,plain,(
% 1.47/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f6])).
% 1.47/0.60  fof(f6,axiom,(
% 1.47/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.47/0.60  fof(f37,plain,(
% 1.47/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.47/0.60    inference(cnf_transformation,[],[f16])).
% 1.47/0.60  fof(f16,plain,(
% 1.47/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.60    inference(ennf_transformation,[],[f5])).
% 1.47/0.60  fof(f5,axiom,(
% 1.47/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.60  fof(f45,plain,(
% 1.47/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.47/0.60    inference(cnf_transformation,[],[f20])).
% 1.47/0.60  fof(f20,plain,(
% 1.47/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.47/0.60    inference(ennf_transformation,[],[f4])).
% 1.47/0.60  fof(f4,axiom,(
% 1.47/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.47/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.47/0.60  fof(f32,plain,(
% 1.47/0.60    ~r1_tarski(sK0,sK1)),
% 1.47/0.60    inference(cnf_transformation,[],[f24])).
% 1.47/0.60  % SZS output end Proof for theBenchmark
% 1.47/0.60  % (12117)------------------------------
% 1.47/0.60  % (12117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.60  % (12117)Termination reason: Refutation
% 1.47/0.60  
% 1.47/0.60  % (12117)Memory used [KB]: 2686
% 1.47/0.60  % (12117)Time elapsed: 0.136 s
% 1.47/0.60  % (12117)------------------------------
% 1.47/0.60  % (12117)------------------------------
% 1.47/0.60  % (12109)Success in time 0.243 s
%------------------------------------------------------------------------------
