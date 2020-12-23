%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:34 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 122 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 ( 348 expanded)
%              Number of equality atoms :   30 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2126,f32])).

fof(f32,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f2126,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f419,f2064])).

fof(f2064,plain,(
    sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f1246,f31])).

fof(f31,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f1246,plain,(
    ! [X19,X18] :
      ( ~ r1_tarski(X19,X18)
      | k2_xboole_0(X19,X18) = X18 ) ),
    inference(subsumption_resolution,[],[f1203,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1203,plain,(
    ! [X19,X18] :
      ( ~ r1_tarski(X18,k2_xboole_0(X19,X18))
      | k2_xboole_0(X19,X18) = X18
      | ~ r1_tarski(X19,X18) ) ),
    inference(superposition,[],[f80,f1128])).

fof(f1128,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f1082,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f1082,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f907,f59])).

fof(f59,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f58,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f907,plain,(
    ! [X4,X5] : r1_tarski(k2_xboole_0(X4,k10_relat_1(k6_relat_1(X4),X5)),X4) ),
    inference(superposition,[],[f55,f203])).

fof(f203,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f91,f59])).

fof(f91,plain,(
    ! [X4,X2,X3] : k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f80,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X5,X6),k2_xboole_0(X4,X6))
      | k2_xboole_0(X5,X6) = k2_xboole_0(X4,X6)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f46,f44])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f419,plain,(
    ! [X20] : r1_tarski(sK0,k10_relat_1(sK2,k2_xboole_0(k9_relat_1(sK2,sK0),X20))) ),
    inference(resolution,[],[f163,f140])).

fof(f140,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f87,f30])).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f163,plain,(
    ! [X17,X18,X16] :
      ( ~ r1_tarski(X18,k10_relat_1(sK2,X16))
      | r1_tarski(X18,k10_relat_1(sK2,k2_xboole_0(X16,X17))) ) ),
    inference(superposition,[],[f72,f90])).

fof(f90,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f45,f28])).

fof(f72,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X2,k2_xboole_0(X3,X4))
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (11864)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (11873)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (11862)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (11863)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (11860)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (11880)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (11877)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (11861)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (11859)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (11874)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (11869)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (11875)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (11881)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (11879)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (11882)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (11871)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (11870)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (11876)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (11865)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (11867)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (11866)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (11883)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (11868)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (11872)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (11884)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (11878)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.29/0.70  % (11875)Refutation found. Thanks to Tanya!
% 2.29/0.70  % SZS status Theorem for theBenchmark
% 2.29/0.70  % SZS output start Proof for theBenchmark
% 2.29/0.70  fof(f2183,plain,(
% 2.29/0.70    $false),
% 2.29/0.70    inference(subsumption_resolution,[],[f2126,f32])).
% 2.29/0.70  fof(f32,plain,(
% 2.29/0.70    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 2.29/0.70    inference(cnf_transformation,[],[f25])).
% 2.29/0.70  fof(f25,plain,(
% 2.29/0.70    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.29/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 2.29/0.70  fof(f24,plain,(
% 2.29/0.70    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.29/0.70    introduced(choice_axiom,[])).
% 2.29/0.70  fof(f15,plain,(
% 2.29/0.70    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.29/0.70    inference(flattening,[],[f14])).
% 2.29/0.70  fof(f14,plain,(
% 2.29/0.70    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.29/0.70    inference(ennf_transformation,[],[f13])).
% 2.29/0.70  fof(f13,negated_conjecture,(
% 2.29/0.70    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.29/0.70    inference(negated_conjecture,[],[f12])).
% 2.29/0.70  fof(f12,conjecture,(
% 2.29/0.70    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.29/0.70  fof(f2126,plain,(
% 2.29/0.70    r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 2.29/0.70    inference(superposition,[],[f419,f2064])).
% 2.29/0.70  fof(f2064,plain,(
% 2.29/0.70    sK1 = k2_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 2.29/0.70    inference(resolution,[],[f1246,f31])).
% 2.29/0.70  fof(f31,plain,(
% 2.29/0.70    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 2.29/0.70    inference(cnf_transformation,[],[f25])).
% 2.29/0.70  fof(f1246,plain,(
% 2.29/0.70    ( ! [X19,X18] : (~r1_tarski(X19,X18) | k2_xboole_0(X19,X18) = X18) )),
% 2.29/0.70    inference(subsumption_resolution,[],[f1203,f50])).
% 2.29/0.70  fof(f50,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.29/0.70    inference(superposition,[],[f38,f39])).
% 2.29/0.70  fof(f39,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f1])).
% 2.29/0.70  fof(f1,axiom,(
% 2.29/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.29/0.70  fof(f38,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f4])).
% 2.29/0.70  fof(f4,axiom,(
% 2.29/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.29/0.70  fof(f1203,plain,(
% 2.29/0.70    ( ! [X19,X18] : (~r1_tarski(X18,k2_xboole_0(X19,X18)) | k2_xboole_0(X19,X18) = X18 | ~r1_tarski(X19,X18)) )),
% 2.29/0.70    inference(superposition,[],[f80,f1128])).
% 2.29/0.70  fof(f1128,plain,(
% 2.29/0.70    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 2.29/0.70    inference(resolution,[],[f1082,f65])).
% 2.29/0.70  fof(f65,plain,(
% 2.29/0.70    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 2.29/0.70    inference(resolution,[],[f44,f38])).
% 2.29/0.70  fof(f44,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f27])).
% 2.29/0.70  fof(f27,plain,(
% 2.29/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.70    inference(flattening,[],[f26])).
% 2.29/0.70  fof(f26,plain,(
% 2.29/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.29/0.70    inference(nnf_transformation,[],[f2])).
% 2.29/0.70  fof(f2,axiom,(
% 2.29/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.29/0.70  fof(f1082,plain,(
% 2.29/0.70    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,X0),X0)) )),
% 2.29/0.70    inference(superposition,[],[f907,f59])).
% 2.29/0.70  fof(f59,plain,(
% 2.29/0.70    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.29/0.70    inference(forward_demodulation,[],[f58,f35])).
% 2.29/0.70  fof(f35,plain,(
% 2.29/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f9])).
% 2.29/0.70  fof(f9,axiom,(
% 2.29/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.29/0.70  fof(f58,plain,(
% 2.29/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.29/0.70    inference(forward_demodulation,[],[f57,f36])).
% 2.29/0.70  fof(f36,plain,(
% 2.29/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f9])).
% 2.29/0.70  fof(f57,plain,(
% 2.29/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.29/0.70    inference(resolution,[],[f37,f33])).
% 2.29/0.70  fof(f33,plain,(
% 2.29/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f10])).
% 2.29/0.70  fof(f10,axiom,(
% 2.29/0.70    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.29/0.70  fof(f37,plain,(
% 2.29/0.70    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f16])).
% 2.29/0.70  fof(f16,plain,(
% 2.29/0.70    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.29/0.70    inference(ennf_transformation,[],[f7])).
% 2.29/0.70  fof(f7,axiom,(
% 2.29/0.70    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.29/0.70  fof(f907,plain,(
% 2.29/0.70    ( ! [X4,X5] : (r1_tarski(k2_xboole_0(X4,k10_relat_1(k6_relat_1(X4),X5)),X4)) )),
% 2.29/0.70    inference(superposition,[],[f55,f203])).
% 2.29/0.70  fof(f203,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.29/0.70    inference(superposition,[],[f91,f59])).
% 2.29/0.70  fof(f91,plain,(
% 2.29/0.70    ( ! [X4,X2,X3] : (k10_relat_1(k6_relat_1(X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k10_relat_1(k6_relat_1(X2),X3),k10_relat_1(k6_relat_1(X2),X4))) )),
% 2.29/0.70    inference(resolution,[],[f45,f33])).
% 2.29/0.70  fof(f45,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f20])).
% 2.29/0.70  fof(f20,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.29/0.70    inference(ennf_transformation,[],[f8])).
% 2.29/0.70  fof(f8,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 2.29/0.70  fof(f55,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.29/0.70    inference(subsumption_resolution,[],[f54,f33])).
% 2.29/0.70  fof(f54,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.29/0.70    inference(superposition,[],[f40,f35])).
% 2.29/0.70  fof(f40,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f17])).
% 2.29/0.70  fof(f17,plain,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.29/0.70    inference(ennf_transformation,[],[f6])).
% 2.29/0.70  fof(f6,axiom,(
% 2.29/0.70    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.29/0.70  fof(f80,plain,(
% 2.29/0.70    ( ! [X6,X4,X5] : (~r1_tarski(k2_xboole_0(X5,X6),k2_xboole_0(X4,X6)) | k2_xboole_0(X5,X6) = k2_xboole_0(X4,X6) | ~r1_tarski(X4,X5)) )),
% 2.29/0.70    inference(resolution,[],[f46,f44])).
% 2.29/0.70  fof(f46,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f21])).
% 2.29/0.70  fof(f21,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 2.29/0.70    inference(ennf_transformation,[],[f5])).
% 2.29/0.70  fof(f5,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 2.29/0.70  fof(f419,plain,(
% 2.29/0.70    ( ! [X20] : (r1_tarski(sK0,k10_relat_1(sK2,k2_xboole_0(k9_relat_1(sK2,sK0),X20)))) )),
% 2.29/0.70    inference(resolution,[],[f163,f140])).
% 2.29/0.70  fof(f140,plain,(
% 2.29/0.70    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 2.29/0.70    inference(resolution,[],[f87,f30])).
% 2.29/0.70  fof(f30,plain,(
% 2.29/0.70    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.29/0.70    inference(cnf_transformation,[],[f25])).
% 2.29/0.70  fof(f87,plain,(
% 2.29/0.70    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))) )),
% 2.29/0.70    inference(resolution,[],[f41,f28])).
% 2.29/0.70  fof(f28,plain,(
% 2.29/0.70    v1_relat_1(sK2)),
% 2.29/0.70    inference(cnf_transformation,[],[f25])).
% 2.29/0.70  fof(f41,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f19])).
% 2.29/0.70  fof(f19,plain,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.29/0.70    inference(flattening,[],[f18])).
% 2.29/0.70  fof(f18,plain,(
% 2.29/0.70    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.29/0.70    inference(ennf_transformation,[],[f11])).
% 2.29/0.70  fof(f11,axiom,(
% 2.29/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.29/0.70  fof(f163,plain,(
% 2.29/0.70    ( ! [X17,X18,X16] : (~r1_tarski(X18,k10_relat_1(sK2,X16)) | r1_tarski(X18,k10_relat_1(sK2,k2_xboole_0(X16,X17)))) )),
% 2.29/0.70    inference(superposition,[],[f72,f90])).
% 2.29/0.70  fof(f90,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 2.29/0.70    inference(resolution,[],[f45,f28])).
% 2.29/0.70  fof(f72,plain,(
% 2.29/0.70    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X4)) | ~r1_tarski(X2,X3)) )),
% 2.29/0.70    inference(resolution,[],[f47,f38])).
% 2.29/0.70  fof(f47,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f23])).
% 2.29/0.70  fof(f23,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.29/0.70    inference(flattening,[],[f22])).
% 2.29/0.70  fof(f22,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.29/0.70    inference(ennf_transformation,[],[f3])).
% 2.29/0.70  fof(f3,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.29/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.29/0.70  % SZS output end Proof for theBenchmark
% 2.29/0.70  % (11875)------------------------------
% 2.29/0.70  % (11875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.70  % (11875)Termination reason: Refutation
% 2.29/0.70  
% 2.29/0.70  % (11875)Memory used [KB]: 3070
% 2.29/0.70  % (11875)Time elapsed: 0.296 s
% 2.29/0.70  % (11875)------------------------------
% 2.29/0.70  % (11875)------------------------------
% 2.29/0.71  % (11858)Success in time 0.352 s
%------------------------------------------------------------------------------
