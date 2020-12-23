%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:19 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 179 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 ( 644 expanded)
%              Number of equality atoms :   37 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1125,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1098,f28])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f1098,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f224,f1083])).

fof(f1083,plain,(
    sK0 = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1082,f50])).

fof(f50,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1082,plain,(
    k3_xboole_0(sK0,k2_relat_1(sK2)) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1081,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1081,plain,(
    k3_xboole_0(k2_relat_1(sK2),sK0) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1057,f144])).

fof(f144,plain,(
    ! [X0] : k3_xboole_0(k2_relat_1(sK2),X0) = k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0))) ),
    inference(resolution,[],[f65,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f64,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1057,plain,(
    k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),sK0))) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f144,f209])).

fof(f209,plain,(
    ! [X0] : k10_relat_1(sK2,k3_xboole_0(X0,sK0)) = k10_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f207,f72])).

fof(f72,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f38,f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f207,plain,(
    ! [X0] : k10_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f72,f147])).

fof(f147,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f72,f49])).

fof(f49,plain,(
    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f224,plain,(
    ! [X6,X7,X5] : r1_tarski(k3_xboole_0(X7,k3_xboole_0(X5,X6)),X6) ),
    inference(superposition,[],[f139,f52])).

fof(f52,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X3) = X3 ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f29,f30])).

fof(f139,plain,(
    ! [X6,X7,X5] : r1_tarski(k3_xboole_0(X5,X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f69,f52])).

fof(f69,plain,(
    ! [X6,X8,X7] : r1_tarski(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8)) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (8887)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (8865)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (8867)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8871)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (8868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (8873)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (8885)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (8875)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (8869)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (8870)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (8864)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (8888)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (8879)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (8866)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (8884)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (8886)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (8881)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (8872)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8878)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (8880)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (8877)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (8874)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (8889)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (8876)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (8882)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (8883)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.79/0.59  % (8880)Refutation found. Thanks to Tanya!
% 1.79/0.59  % SZS status Theorem for theBenchmark
% 1.79/0.59  % SZS output start Proof for theBenchmark
% 1.79/0.59  fof(f1125,plain,(
% 1.79/0.59    $false),
% 1.79/0.59    inference(subsumption_resolution,[],[f1098,f28])).
% 1.79/0.59  fof(f28,plain,(
% 1.79/0.59    ~r1_tarski(sK0,sK1)),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f21,plain,(
% 1.79/0.59    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 1.79/0.59  fof(f20,plain,(
% 1.79/0.59    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f12,plain,(
% 1.79/0.59    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.79/0.59    inference(flattening,[],[f11])).
% 1.79/0.59  fof(f11,plain,(
% 1.79/0.59    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.79/0.59    inference(ennf_transformation,[],[f10])).
% 1.79/0.59  fof(f10,negated_conjecture,(
% 1.79/0.59    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.79/0.59    inference(negated_conjecture,[],[f9])).
% 1.79/0.59  fof(f9,conjecture,(
% 1.79/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.79/0.59  fof(f1098,plain,(
% 1.79/0.59    r1_tarski(sK0,sK1)),
% 1.79/0.59    inference(superposition,[],[f224,f1083])).
% 1.79/0.59  fof(f1083,plain,(
% 1.79/0.59    sK0 = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1))),
% 1.79/0.59    inference(forward_demodulation,[],[f1082,f50])).
% 1.79/0.59  fof(f50,plain,(
% 1.79/0.59    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 1.79/0.59    inference(resolution,[],[f32,f27])).
% 1.79/0.59  fof(f27,plain,(
% 1.79/0.59    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f32,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.79/0.59    inference(cnf_transformation,[],[f14])).
% 1.79/0.59  fof(f14,plain,(
% 1.79/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f6])).
% 1.79/0.59  fof(f6,axiom,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.79/0.59  fof(f1082,plain,(
% 1.79/0.59    k3_xboole_0(sK0,k2_relat_1(sK2)) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1))),
% 1.79/0.59    inference(forward_demodulation,[],[f1081,f30])).
% 1.79/0.59  fof(f30,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f1])).
% 1.79/0.59  fof(f1,axiom,(
% 1.79/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.59  fof(f1081,plain,(
% 1.79/0.59    k3_xboole_0(k2_relat_1(sK2),sK0) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1))),
% 1.79/0.59    inference(forward_demodulation,[],[f1057,f144])).
% 1.79/0.59  fof(f144,plain,(
% 1.79/0.59    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK2),X0) = k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)))) )),
% 1.79/0.59    inference(resolution,[],[f65,f29])).
% 1.79/0.59  fof(f29,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f5])).
% 1.79/0.59  fof(f5,axiom,(
% 1.79/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.79/0.59  fof(f65,plain,(
% 1.79/0.59    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) )),
% 1.79/0.59    inference(subsumption_resolution,[],[f64,f24])).
% 1.79/0.59  fof(f24,plain,(
% 1.79/0.59    v1_relat_1(sK2)),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f64,plain,(
% 1.79/0.59    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) )),
% 1.79/0.59    inference(resolution,[],[f33,f25])).
% 1.79/0.59  fof(f25,plain,(
% 1.79/0.59    v1_funct_1(sK2)),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f33,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f16])).
% 1.79/0.59  fof(f16,plain,(
% 1.79/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.79/0.59    inference(flattening,[],[f15])).
% 1.79/0.59  fof(f15,plain,(
% 1.79/0.59    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.79/0.59    inference(ennf_transformation,[],[f8])).
% 1.79/0.59  fof(f8,axiom,(
% 1.79/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.79/0.59  fof(f1057,plain,(
% 1.79/0.59    k9_relat_1(sK2,k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),sK0))) = k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,sK1))),
% 1.79/0.59    inference(superposition,[],[f144,f209])).
% 1.79/0.59  fof(f209,plain,(
% 1.79/0.59    ( ! [X0] : (k10_relat_1(sK2,k3_xboole_0(X0,sK0)) = k10_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 1.79/0.59    inference(forward_demodulation,[],[f207,f72])).
% 1.79/0.59  fof(f72,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.79/0.59    inference(subsumption_resolution,[],[f71,f24])).
% 1.79/0.59  fof(f71,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.79/0.59    inference(resolution,[],[f38,f25])).
% 1.79/0.59  fof(f38,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f19])).
% 1.79/0.59  fof(f19,plain,(
% 1.79/0.59    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.79/0.59    inference(flattening,[],[f18])).
% 1.79/0.59  fof(f18,plain,(
% 1.79/0.59    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.79/0.59    inference(ennf_transformation,[],[f7])).
% 1.79/0.59  fof(f7,axiom,(
% 1.79/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).
% 1.79/0.59  fof(f207,plain,(
% 1.79/0.59    ( ! [X0] : (k10_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,sK0))) )),
% 1.79/0.59    inference(superposition,[],[f72,f147])).
% 1.79/0.59  fof(f147,plain,(
% 1.79/0.59    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 1.79/0.59    inference(superposition,[],[f72,f49])).
% 1.79/0.59  fof(f49,plain,(
% 1.79/0.59    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.79/0.59    inference(resolution,[],[f32,f26])).
% 1.79/0.59  fof(f26,plain,(
% 1.79/0.59    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f224,plain,(
% 1.79/0.59    ( ! [X6,X7,X5] : (r1_tarski(k3_xboole_0(X7,k3_xboole_0(X5,X6)),X6)) )),
% 1.79/0.59    inference(superposition,[],[f139,f52])).
% 1.79/0.59  fof(f52,plain,(
% 1.79/0.59    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X3) = X3) )),
% 1.79/0.59    inference(resolution,[],[f41,f31])).
% 1.79/0.59  fof(f31,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.79/0.59    inference(cnf_transformation,[],[f13])).
% 1.79/0.59  fof(f13,plain,(
% 1.79/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.79/0.59    inference(ennf_transformation,[],[f4])).
% 1.79/0.59  fof(f4,axiom,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.79/0.59  fof(f41,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.79/0.59    inference(superposition,[],[f29,f30])).
% 1.79/0.59  fof(f139,plain,(
% 1.79/0.59    ( ! [X6,X7,X5] : (r1_tarski(k3_xboole_0(X5,X6),k2_xboole_0(X6,X7))) )),
% 1.79/0.59    inference(superposition,[],[f69,f52])).
% 1.79/0.59  fof(f69,plain,(
% 1.79/0.59    ( ! [X6,X8,X7] : (r1_tarski(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8))) )),
% 1.79/0.59    inference(resolution,[],[f55,f37])).
% 1.79/0.59  fof(f37,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f17])).
% 1.79/0.59  fof(f17,plain,(
% 1.79/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.79/0.59    inference(ennf_transformation,[],[f3])).
% 1.79/0.59  fof(f3,axiom,(
% 1.79/0.59    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.79/0.59  fof(f55,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.79/0.59    inference(resolution,[],[f37,f39])).
% 1.79/0.59  fof(f39,plain,(
% 1.79/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.79/0.59    inference(equality_resolution,[],[f35])).
% 1.79/0.59  fof(f35,plain,(
% 1.79/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.79/0.59    inference(cnf_transformation,[],[f23])).
% 1.79/0.59  fof(f23,plain,(
% 1.79/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.59    inference(flattening,[],[f22])).
% 1.79/0.59  fof(f22,plain,(
% 1.79/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.59    inference(nnf_transformation,[],[f2])).
% 1.79/0.59  fof(f2,axiom,(
% 1.79/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.59  % SZS output end Proof for theBenchmark
% 1.79/0.59  % (8880)------------------------------
% 1.79/0.59  % (8880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (8880)Termination reason: Refutation
% 1.79/0.59  
% 1.79/0.59  % (8880)Memory used [KB]: 2302
% 1.79/0.59  % (8880)Time elapsed: 0.165 s
% 1.79/0.59  % (8880)------------------------------
% 1.79/0.59  % (8880)------------------------------
% 1.79/0.59  % (8863)Success in time 0.232 s
%------------------------------------------------------------------------------
