%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 368 expanded)
%              Number of leaves         :   11 (  92 expanded)
%              Depth                    :   18
%              Number of atoms          :  175 (1304 expanded)
%              Number of equality atoms :   43 ( 173 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f43,f291,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f291,plain,(
    ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f290,f50])).

fof(f50,plain,(
    k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).

fof(f21,plain,
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

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

% (11104)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f290,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f199,f289])).

fof(f289,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f288,f263])).

fof(f263,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f256,f183])).

fof(f183,plain,(
    ! [X4] : k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X4,X4)) ),
    inference(resolution,[],[f89,f47])).

% (11076)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (11084)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (11096)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3))
      | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X3)) ) ),
    inference(superposition,[],[f80,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f79,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f256,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X0)),X1) ),
    inference(resolution,[],[f90,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,X0),k2_xboole_0(k10_relat_1(sK2,X1),X2))
      | r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X1)),X2) ) ),
    inference(superposition,[],[f46,f80])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f288,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f282,f276])).

fof(f276,plain,(
    ! [X7] : k1_xboole_0 = k6_subset_1(X7,X7) ),
    inference(resolution,[],[f263,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_subset_1(X0,X0))
      | k6_subset_1(X0,X0) = X1 ) ),
    inference(resolution,[],[f69,f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | k6_subset_1(X0,X1) = X2
      | ~ r1_tarski(X2,k6_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f282,plain,(
    ! [X13] :
      ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
      | ~ r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f238,f276])).

fof(f238,plain,(
    ! [X13] :
      ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13)
      | ~ r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f237,f26])).

fof(f237,plain,(
    ! [X13] :
      ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13)
      | ~ r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f224,f27])).

fof(f224,plain,(
    ! [X13] :
      ( k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13)
      | ~ r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f34,f183])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f199,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f198,f26])).

fof(f198,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f27])).

fof(f194,plain,
    ( k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f34,f180])).

% (11095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f180,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f89,f28])).

fof(f28,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f29,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (11075)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (11085)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (11097)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (11083)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (11081)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (11077)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.58  % (11080)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.58  % (11079)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.58  % (11078)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.58  % (11100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.58  % (11098)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (11090)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (11097)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.60  % (11103)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.60  % (11102)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.60  % (11101)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.68/0.60  % (11082)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.68/0.60  % SZS output start Proof for theBenchmark
% 1.68/0.60  fof(f338,plain,(
% 1.68/0.60    $false),
% 1.68/0.60    inference(unit_resulting_resolution,[],[f29,f43,f291,f42])).
% 1.68/0.60  fof(f42,plain,(
% 1.68/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f20])).
% 1.68/0.60  fof(f20,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.68/0.60    inference(flattening,[],[f19])).
% 1.68/0.60  fof(f19,plain,(
% 1.68/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.68/0.60    inference(ennf_transformation,[],[f3])).
% 1.68/0.60  fof(f3,axiom,(
% 1.68/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.68/0.60  fof(f291,plain,(
% 1.68/0.60    ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))),
% 1.68/0.60    inference(subsumption_resolution,[],[f290,f50])).
% 1.68/0.60  fof(f50,plain,(
% 1.68/0.60    k1_xboole_0 != k6_subset_1(sK0,sK1)),
% 1.68/0.60    inference(resolution,[],[f45,f30])).
% 1.68/0.60  fof(f30,plain,(
% 1.68/0.60    ~r1_tarski(sK0,sK1)),
% 1.68/0.60    inference(cnf_transformation,[],[f22])).
% 1.68/0.60  fof(f22,plain,(
% 1.68/0.60    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.68/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21])).
% 1.68/0.60  fof(f21,plain,(
% 1.68/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.68/0.60    introduced(choice_axiom,[])).
% 1.68/0.60  fof(f13,plain,(
% 1.68/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.68/0.60    inference(flattening,[],[f12])).
% 1.68/0.60  % (11104)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.60  fof(f12,plain,(
% 1.68/0.60    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.68/0.60    inference(ennf_transformation,[],[f11])).
% 1.68/0.60  fof(f11,negated_conjecture,(
% 1.68/0.60    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.68/0.60    inference(negated_conjecture,[],[f10])).
% 1.68/0.60  fof(f10,conjecture,(
% 1.68/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 1.68/0.60  fof(f45,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 1.68/0.60    inference(definition_unfolding,[],[f38,f33])).
% 1.68/0.60  fof(f33,plain,(
% 1.68/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.68/0.60    inference(cnf_transformation,[],[f7])).
% 1.68/0.60  fof(f7,axiom,(
% 1.68/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.68/0.60  fof(f38,plain,(
% 1.68/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.68/0.60    inference(cnf_transformation,[],[f25])).
% 1.68/0.60  fof(f25,plain,(
% 1.68/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.68/0.60    inference(nnf_transformation,[],[f2])).
% 1.68/0.60  fof(f2,axiom,(
% 1.68/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.68/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.68/0.60  fof(f290,plain,(
% 1.68/0.60    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))),
% 1.68/0.60    inference(backward_demodulation,[],[f199,f289])).
% 1.68/0.60  fof(f289,plain,(
% 1.68/0.60    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.68/0.60    inference(subsumption_resolution,[],[f288,f263])).
% 1.68/0.60  fof(f263,plain,(
% 1.68/0.60    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.68/0.60    inference(forward_demodulation,[],[f256,f183])).
% 1.68/0.60  fof(f183,plain,(
% 1.68/0.60    ( ! [X4] : (k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X4,X4))) )),
% 1.68/0.60    inference(resolution,[],[f89,f47])).
% 1.68/0.61  % (11076)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.68/0.61  % (11084)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.68/0.61  % (11096)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.68/0.61  fof(f47,plain,(
% 1.68/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.68/0.61    inference(equality_resolution,[],[f36])).
% 1.68/0.61  fof(f36,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.68/0.61    inference(cnf_transformation,[],[f24])).
% 1.68/0.61  fof(f24,plain,(
% 1.68/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.61    inference(flattening,[],[f23])).
% 1.68/0.61  fof(f23,plain,(
% 1.68/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.68/0.61    inference(nnf_transformation,[],[f1])).
% 1.68/0.61  fof(f1,axiom,(
% 1.68/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.68/0.61  fof(f89,plain,(
% 1.68/0.61    ( ! [X2,X3] : (~r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) | k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(X2,X3))) )),
% 1.68/0.61    inference(superposition,[],[f80,f44])).
% 1.68/0.61  fof(f44,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f39,f33])).
% 1.68/0.61  fof(f39,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f25])).
% 1.68/0.61  fof(f80,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.68/0.61    inference(subsumption_resolution,[],[f79,f26])).
% 1.68/0.61  fof(f26,plain,(
% 1.68/0.61    v1_relat_1(sK2)),
% 1.68/0.61    inference(cnf_transformation,[],[f22])).
% 1.68/0.61  fof(f79,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 1.68/0.61    inference(resolution,[],[f41,f27])).
% 1.68/0.61  fof(f27,plain,(
% 1.68/0.61    v1_funct_1(sK2)),
% 1.68/0.61    inference(cnf_transformation,[],[f22])).
% 1.68/0.61  fof(f41,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f18])).
% 1.68/0.61  fof(f18,plain,(
% 1.68/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.68/0.61    inference(flattening,[],[f17])).
% 1.68/0.61  fof(f17,plain,(
% 1.68/0.61    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.68/0.61    inference(ennf_transformation,[],[f8])).
% 1.68/0.61  fof(f8,axiom,(
% 1.68/0.61    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 1.68/0.61  fof(f256,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X0)),X1)) )),
% 1.68/0.61    inference(resolution,[],[f90,f31])).
% 1.68/0.61  fof(f31,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f6])).
% 1.68/0.61  fof(f6,axiom,(
% 1.68/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.68/0.61  fof(f90,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(sK2,X0),k2_xboole_0(k10_relat_1(sK2,X1),X2)) | r1_tarski(k10_relat_1(sK2,k6_subset_1(X0,X1)),X2)) )),
% 1.68/0.61    inference(superposition,[],[f46,f80])).
% 1.68/0.61  fof(f46,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.68/0.61    inference(definition_unfolding,[],[f40,f33])).
% 1.68/0.61  fof(f40,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.68/0.61    inference(cnf_transformation,[],[f16])).
% 1.68/0.61  fof(f16,plain,(
% 1.68/0.61    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.68/0.61    inference(ennf_transformation,[],[f5])).
% 1.68/0.61  fof(f5,axiom,(
% 1.68/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.68/0.61  fof(f288,plain,(
% 1.68/0.61    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.68/0.61    inference(forward_demodulation,[],[f282,f276])).
% 1.68/0.61  fof(f276,plain,(
% 1.68/0.61    ( ! [X7] : (k1_xboole_0 = k6_subset_1(X7,X7)) )),
% 1.68/0.61    inference(resolution,[],[f263,f147])).
% 1.68/0.61  fof(f147,plain,(
% 1.68/0.61    ( ! [X0,X1] : (~r1_tarski(X1,k6_subset_1(X0,X0)) | k6_subset_1(X0,X0) = X1) )),
% 1.68/0.61    inference(resolution,[],[f69,f31])).
% 1.68/0.61  fof(f69,plain,(
% 1.68/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | k6_subset_1(X0,X1) = X2 | ~r1_tarski(X2,k6_subset_1(X0,X1))) )),
% 1.68/0.61    inference(resolution,[],[f46,f37])).
% 1.68/0.61  fof(f37,plain,(
% 1.68/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f24])).
% 1.68/0.61  fof(f282,plain,(
% 1.68/0.61    ( ! [X13] : (k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2))) )),
% 1.68/0.61    inference(backward_demodulation,[],[f238,f276])).
% 1.68/0.61  fof(f238,plain,(
% 1.68/0.61    ( ! [X13] : (k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13) | ~r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2))) )),
% 1.68/0.61    inference(subsumption_resolution,[],[f237,f26])).
% 1.68/0.61  fof(f237,plain,(
% 1.68/0.61    ( ! [X13] : (k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13) | ~r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.68/0.61    inference(subsumption_resolution,[],[f224,f27])).
% 1.68/0.61  fof(f224,plain,(
% 1.68/0.61    ( ! [X13] : (k9_relat_1(sK2,k1_xboole_0) = k6_subset_1(X13,X13) | ~r1_tarski(k6_subset_1(X13,X13),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.68/0.61    inference(superposition,[],[f34,f183])).
% 1.68/0.61  fof(f34,plain,(
% 1.68/0.61    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f15])).
% 1.68/0.61  fof(f15,plain,(
% 1.68/0.61    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.68/0.61    inference(flattening,[],[f14])).
% 1.68/0.61  fof(f14,plain,(
% 1.68/0.61    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.68/0.61    inference(ennf_transformation,[],[f9])).
% 1.68/0.61  fof(f9,axiom,(
% 1.68/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.68/0.61  fof(f199,plain,(
% 1.68/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))),
% 1.68/0.61    inference(subsumption_resolution,[],[f198,f26])).
% 1.68/0.61  fof(f198,plain,(
% 1.68/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.68/0.61    inference(subsumption_resolution,[],[f194,f27])).
% 1.68/0.61  fof(f194,plain,(
% 1.68/0.61    k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.68/0.61    inference(superposition,[],[f34,f180])).
% 1.68/0.61  % (11095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.68/0.61  fof(f180,plain,(
% 1.68/0.61    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.68/0.61    inference(resolution,[],[f89,f28])).
% 1.68/0.61  fof(f28,plain,(
% 1.68/0.61    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.68/0.61    inference(cnf_transformation,[],[f22])).
% 1.68/0.61  fof(f43,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.68/0.61    inference(definition_unfolding,[],[f32,f33])).
% 1.68/0.61  fof(f32,plain,(
% 1.68/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.68/0.61    inference(cnf_transformation,[],[f4])).
% 1.68/0.61  fof(f4,axiom,(
% 1.68/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.68/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.68/0.61  fof(f29,plain,(
% 1.68/0.61    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.68/0.61    inference(cnf_transformation,[],[f22])).
% 1.68/0.61  % SZS output end Proof for theBenchmark
% 1.68/0.61  % (11097)------------------------------
% 1.68/0.61  % (11097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (11097)Termination reason: Refutation
% 1.68/0.61  
% 1.68/0.61  % (11097)Memory used [KB]: 6524
% 1.68/0.61  % (11097)Time elapsed: 0.167 s
% 1.68/0.61  % (11097)------------------------------
% 1.68/0.61  % (11097)------------------------------
% 1.68/0.61  % (11089)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.68/0.62  % (11074)Success in time 0.249 s
%------------------------------------------------------------------------------
