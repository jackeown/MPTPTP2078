%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:28 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 325 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 567 expanded)
%              Number of equality atoms :   42 ( 252 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f604,plain,(
    $false ),
    inference(subsumption_resolution,[],[f602,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f52,f134])).

fof(f134,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f48,f86,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f86,plain,(
    ! [X0] : r1_tarski(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_subset_1(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f74,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,k6_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f32,f35,f35])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f602,plain,(
    k1_xboole_0 != k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f316,f598])).

fof(f598,plain,(
    ! [X2,X3] : k9_relat_1(sK2,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f597,f134])).

fof(f597,plain,(
    ! [X2,X3] : k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k1_xboole_0) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f596,f55])).

fof(f55,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f596,plain,(
    ! [X2,X3] : k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f563,f137])).

fof(f563,plain,(
    ! [X2,X3] : k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,k6_subset_1(k6_subset_1(X2,X3),k6_subset_1(X2,X3)))) ),
    inference(superposition,[],[f217,f182])).

fof(f182,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f48,f83,f31])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1)) ),
    inference(unit_resulting_resolution,[],[f53,f49,f47])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f217,plain,(
    ! [X2,X3] : k6_subset_1(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,X2),k9_relat_1(sK2,k6_subset_1(X2,k6_subset_1(X2,X3)))) ),
    inference(superposition,[],[f45,f105])).

fof(f105,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(unit_resulting_resolution,[],[f27,f25,f26,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f36,f44,f44])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f35,f35,f44])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f316,plain,(
    k1_xboole_0 != k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))) ),
    inference(unit_resulting_resolution,[],[f296,f51])).

fof(f296,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f295,f250])).

fof(f250,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f220,f45])).

fof(f220,plain,(
    ! [X10,X9] : r1_tarski(k9_relat_1(sK2,k6_subset_1(X9,k6_subset_1(X9,X10))),k9_relat_1(sK2,X9)) ),
    inference(superposition,[],[f48,f105])).

fof(f295,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f294,f103])).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f294,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f58,f47])).

fof(f58,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(extensionality_resolution,[],[f31,f28])).

fof(f28,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (32704)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (32711)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.53  % (32699)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (32719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (32693)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.54  % (32705)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.54  % (32717)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.54  % (32709)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.54  % (32715)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.54  % (32720)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.54  % (32694)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.40/0.54  % (32701)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.54  % (32696)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.54  % (32707)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.54  % (32709)Refutation not found, incomplete strategy% (32709)------------------------------
% 1.40/0.54  % (32709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (32709)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (32709)Memory used [KB]: 10618
% 1.40/0.55  % (32708)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.55  % (32710)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (32697)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.55  % (32712)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (32700)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.40/0.55  % (32709)Time elapsed: 0.128 s
% 1.40/0.55  % (32709)------------------------------
% 1.40/0.55  % (32709)------------------------------
% 1.40/0.56  % (32702)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (32695)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.56  % (32718)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.56  % (32703)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.56  % (32714)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.56  % (32703)Refutation not found, incomplete strategy% (32703)------------------------------
% 1.40/0.56  % (32703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (32703)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (32703)Memory used [KB]: 10746
% 1.40/0.56  % (32703)Time elapsed: 0.157 s
% 1.40/0.56  % (32703)------------------------------
% 1.40/0.56  % (32703)------------------------------
% 1.40/0.57  % (32721)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.57  % (32721)Refutation not found, incomplete strategy% (32721)------------------------------
% 1.40/0.57  % (32721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (32721)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (32721)Memory used [KB]: 10746
% 1.40/0.57  % (32721)Time elapsed: 0.159 s
% 1.40/0.57  % (32721)------------------------------
% 1.40/0.57  % (32721)------------------------------
% 1.40/0.57  % (32706)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.57  % (32716)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.57  % (32698)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.58  % (32722)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.58  % (32722)Refutation not found, incomplete strategy% (32722)------------------------------
% 1.40/0.58  % (32722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (32722)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.58  
% 1.40/0.58  % (32722)Memory used [KB]: 1663
% 1.40/0.58  % (32722)Time elapsed: 0.136 s
% 1.40/0.58  % (32722)------------------------------
% 1.40/0.58  % (32722)------------------------------
% 1.40/0.58  % (32713)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.58  % (32712)Refutation found. Thanks to Tanya!
% 1.40/0.58  % SZS status Theorem for theBenchmark
% 1.40/0.58  % SZS output start Proof for theBenchmark
% 1.40/0.58  fof(f604,plain,(
% 1.40/0.58    $false),
% 1.40/0.58    inference(subsumption_resolution,[],[f602,f137])).
% 1.40/0.58  fof(f137,plain,(
% 1.40/0.58    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.40/0.58    inference(backward_demodulation,[],[f52,f134])).
% 1.40/0.58  fof(f134,plain,(
% 1.40/0.58    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f48,f86,f31])).
% 1.40/0.58  fof(f31,plain,(
% 1.40/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.40/0.58    inference(cnf_transformation,[],[f3])).
% 1.40/0.58  fof(f3,axiom,(
% 1.40/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.58  fof(f86,plain,(
% 1.40/0.58    ( ! [X0] : (r1_tarski(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f53,f74,f47])).
% 1.40/0.58  fof(f47,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_subset_1(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f38,f35])).
% 1.40/0.58  fof(f35,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f11])).
% 1.40/0.58  fof(f11,axiom,(
% 1.40/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.40/0.58  fof(f38,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f24])).
% 1.40/0.58  fof(f24,plain,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.40/0.58    inference(flattening,[],[f23])).
% 1.40/0.58  fof(f23,plain,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.40/0.58    inference(ennf_transformation,[],[f10])).
% 1.40/0.58  fof(f10,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.40/0.58  fof(f74,plain,(
% 1.40/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f52,f51])).
% 1.40/0.58  fof(f51,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f41,f44])).
% 1.40/0.58  fof(f44,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f32,f35,f35])).
% 1.40/0.58  fof(f32,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f8])).
% 1.40/0.58  fof(f8,axiom,(
% 1.40/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.40/0.58  fof(f41,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f1])).
% 1.40/0.58  fof(f1,axiom,(
% 1.40/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.40/0.58  fof(f53,plain,(
% 1.40/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.58    inference(equality_resolution,[],[f30])).
% 1.40/0.58  fof(f30,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.40/0.58    inference(cnf_transformation,[],[f3])).
% 1.40/0.58  fof(f48,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f39,f35])).
% 1.40/0.58  fof(f39,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f6])).
% 1.40/0.58  fof(f6,axiom,(
% 1.40/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.40/0.58  fof(f52,plain,(
% 1.40/0.58    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f43,f44])).
% 1.40/0.58  fof(f43,plain,(
% 1.40/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f5])).
% 1.40/0.58  fof(f5,axiom,(
% 1.40/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.40/0.58  fof(f602,plain,(
% 1.40/0.58    k1_xboole_0 != k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.40/0.58    inference(backward_demodulation,[],[f316,f598])).
% 1.40/0.58  fof(f598,plain,(
% 1.40/0.58    ( ! [X2,X3] : (k9_relat_1(sK2,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3))) )),
% 1.40/0.58    inference(forward_demodulation,[],[f597,f134])).
% 1.40/0.58  fof(f597,plain,(
% 1.40/0.58    ( ! [X2,X3] : (k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k1_xboole_0) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3))) )),
% 1.40/0.58    inference(forward_demodulation,[],[f596,f55])).
% 1.40/0.58  fof(f55,plain,(
% 1.40/0.58    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f25,f37])).
% 1.40/0.58  fof(f37,plain,(
% 1.40/0.58    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f22])).
% 1.40/0.58  fof(f22,plain,(
% 1.40/0.58    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.40/0.58    inference(ennf_transformation,[],[f12])).
% 1.40/0.58  fof(f12,axiom,(
% 1.40/0.58    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 1.40/0.58  fof(f25,plain,(
% 1.40/0.58    v1_relat_1(sK2)),
% 1.40/0.58    inference(cnf_transformation,[],[f18])).
% 1.40/0.58  fof(f18,plain,(
% 1.40/0.58    ? [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.40/0.58    inference(flattening,[],[f17])).
% 1.40/0.58  fof(f17,plain,(
% 1.40/0.58    ? [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1)) & v2_funct_1(X2)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.40/0.58    inference(ennf_transformation,[],[f16])).
% 1.40/0.58  fof(f16,negated_conjecture,(
% 1.40/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.40/0.58    inference(negated_conjecture,[],[f15])).
% 1.40/0.58  fof(f15,conjecture,(
% 1.40/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 1.40/0.58  fof(f596,plain,(
% 1.40/0.58    ( ! [X2,X3] : (k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,k1_xboole_0))) )),
% 1.40/0.58    inference(forward_demodulation,[],[f563,f137])).
% 1.40/0.58  fof(f563,plain,(
% 1.40/0.58    ( ! [X2,X3] : (k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,k6_subset_1(X2,X3)),k9_relat_1(sK2,k6_subset_1(k6_subset_1(X2,X3),k6_subset_1(X2,X3))))) )),
% 1.40/0.58    inference(superposition,[],[f217,f182])).
% 1.40/0.58  fof(f182,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k6_subset_1(X0,X1),X1)) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f48,f83,f31])).
% 1.40/0.58  fof(f83,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),k6_subset_1(k6_subset_1(X0,X1),X1))) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f53,f49,f47])).
% 1.40/0.58  fof(f49,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 1.40/0.58    inference(definition_unfolding,[],[f40,f35])).
% 1.40/0.58  fof(f40,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.40/0.58    inference(cnf_transformation,[],[f9])).
% 1.40/0.58  fof(f9,axiom,(
% 1.40/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.40/0.58  fof(f217,plain,(
% 1.40/0.58    ( ! [X2,X3] : (k6_subset_1(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) = k6_subset_1(k9_relat_1(sK2,X2),k9_relat_1(sK2,k6_subset_1(X2,k6_subset_1(X2,X3))))) )),
% 1.40/0.58    inference(superposition,[],[f45,f105])).
% 1.40/0.58  fof(f105,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(sK2,X0),k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f27,f25,f26,f46])).
% 1.40/0.58  fof(f46,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) = k6_subset_1(k9_relat_1(X2,X0),k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f36,f44,f44])).
% 1.40/0.58  fof(f36,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f21])).
% 1.40/0.58  fof(f21,plain,(
% 1.40/0.58    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.58    inference(flattening,[],[f20])).
% 1.40/0.58  fof(f20,plain,(
% 1.40/0.58    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.40/0.58    inference(ennf_transformation,[],[f14])).
% 1.40/0.58  fof(f14,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).
% 1.40/0.58  fof(f26,plain,(
% 1.40/0.58    v1_funct_1(sK2)),
% 1.40/0.58    inference(cnf_transformation,[],[f18])).
% 1.40/0.58  fof(f27,plain,(
% 1.40/0.58    v2_funct_1(sK2)),
% 1.40/0.58    inference(cnf_transformation,[],[f18])).
% 1.40/0.58  fof(f45,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 1.40/0.58    inference(definition_unfolding,[],[f33,f35,f35,f44])).
% 1.40/0.58  fof(f33,plain,(
% 1.40/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f7])).
% 1.40/0.58  fof(f7,axiom,(
% 1.40/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.40/0.58  fof(f316,plain,(
% 1.40/0.58    k1_xboole_0 != k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)))),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f296,f51])).
% 1.40/0.58  fof(f296,plain,(
% 1.40/0.58    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 1.40/0.58    inference(subsumption_resolution,[],[f295,f250])).
% 1.40/0.58  fof(f250,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X0,X1)),k9_relat_1(sK2,X0))) )),
% 1.40/0.58    inference(superposition,[],[f220,f45])).
% 1.40/0.58  fof(f220,plain,(
% 1.40/0.58    ( ! [X10,X9] : (r1_tarski(k9_relat_1(sK2,k6_subset_1(X9,k6_subset_1(X9,X10))),k9_relat_1(sK2,X9))) )),
% 1.40/0.58    inference(superposition,[],[f48,f105])).
% 1.40/0.58  fof(f295,plain,(
% 1.40/0.58    ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.40/0.58    inference(subsumption_resolution,[],[f294,f103])).
% 1.40/0.58  fof(f103,plain,(
% 1.40/0.58    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))) )),
% 1.40/0.58    inference(unit_resulting_resolution,[],[f25,f34])).
% 1.40/0.58  fof(f34,plain,(
% 1.40/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))) )),
% 1.40/0.58    inference(cnf_transformation,[],[f19])).
% 1.40/0.58  fof(f19,plain,(
% 1.40/0.58    ! [X0,X1,X2] : (r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) | ~v1_relat_1(X2))),
% 1.40/0.58    inference(ennf_transformation,[],[f13])).
% 1.40/0.58  fof(f13,axiom,(
% 1.40/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 1.40/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).
% 1.40/0.58  fof(f294,plain,(
% 1.40/0.58    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) | ~r1_xboole_0(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 1.40/0.58    inference(resolution,[],[f58,f47])).
% 1.40/0.58  fof(f58,plain,(
% 1.40/0.58    ~r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) | ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 1.40/0.58    inference(extensionality_resolution,[],[f31,f28])).
% 1.40/0.58  fof(f28,plain,(
% 1.40/0.58    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 1.40/0.58    inference(cnf_transformation,[],[f18])).
% 1.40/0.58  % SZS output end Proof for theBenchmark
% 1.40/0.58  % (32712)------------------------------
% 1.40/0.58  % (32712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.58  % (32712)Termination reason: Refutation
% 1.40/0.58  
% 1.40/0.58  % (32712)Memory used [KB]: 1918
% 1.40/0.58  % (32712)Time elapsed: 0.158 s
% 1.40/0.58  % (32712)------------------------------
% 1.40/0.58  % (32712)------------------------------
% 1.40/0.58  % (32692)Success in time 0.218 s
%------------------------------------------------------------------------------
