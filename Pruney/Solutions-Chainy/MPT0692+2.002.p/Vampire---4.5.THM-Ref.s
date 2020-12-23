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
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 6.42s
% Output     : Refutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 516 expanded)
%              Number of equality atoms :   53 ( 161 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10132,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f35,f506,f3313,f1606,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

fof(f1606,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f36,f35,f96,f104])).

fof(f104,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k10_relat_1(X5,X6),k10_relat_1(X5,X7))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = k10_relat_1(X5,k6_subset_1(X6,X7)) ) ),
    inference(superposition,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f96,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f35,f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f3313,plain,(
    r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) ),
    inference(superposition,[],[f330,f239])).

fof(f239,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f227,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f227,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ),
    inference(unit_resulting_resolution,[],[f93,f92])).

fof(f92,plain,(
    ! [X2,X1] :
      ( k1_setfam_1(k2_tarski(X1,X2)) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f87,f56])).

fof(f56,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_setfam_1(k2_tarski(X1,X2)) = k6_subset_1(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f58,f59])).

fof(f58,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f43,f42,f42])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f93,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f35,f36,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f330,plain,(
    ! [X15] : r1_tarski(k6_subset_1(sK0,k1_setfam_1(k2_tarski(sK0,X15))),k2_relat_1(sK1)) ),
    inference(superposition,[],[f85,f88])).

fof(f88,plain,(
    ! [X4,X3] : k1_setfam_1(k2_tarski(X3,k6_subset_1(X3,X4))) = k6_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4))) ),
    inference(superposition,[],[f58,f58])).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f37,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f37,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f506,plain,(
    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f159,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f93,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f38,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22228)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (22243)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (22227)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (22233)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (22236)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (22237)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (22232)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22230)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (22234)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (22254)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (22238)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (22247)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (22240)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (22246)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (22229)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (22253)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (22231)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (22226)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (22255)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (22239)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (22245)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (22248)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (22241)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (22242)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (22244)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (22235)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (22252)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (22251)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (22250)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  % (22249)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 3.36/0.81  % (22228)Time limit reached!
% 3.36/0.81  % (22228)------------------------------
% 3.36/0.81  % (22228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.81  % (22228)Termination reason: Time limit
% 3.36/0.81  % (22228)Termination phase: Saturation
% 3.36/0.81  
% 3.36/0.81  % (22228)Memory used [KB]: 7036
% 3.36/0.81  % (22228)Time elapsed: 0.400 s
% 3.36/0.81  % (22228)------------------------------
% 3.36/0.81  % (22228)------------------------------
% 3.36/0.82  % (22250)Time limit reached!
% 3.36/0.82  % (22250)------------------------------
% 3.36/0.82  % (22250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.82  % (22250)Termination reason: Time limit
% 3.36/0.82  % (22250)Termination phase: Saturation
% 3.36/0.82  
% 3.36/0.82  % (22250)Memory used [KB]: 12792
% 3.36/0.82  % (22250)Time elapsed: 0.400 s
% 3.36/0.82  % (22250)------------------------------
% 3.36/0.82  % (22250)------------------------------
% 4.21/0.92  % (22232)Time limit reached!
% 4.21/0.92  % (22232)------------------------------
% 4.21/0.92  % (22232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.92  % (22232)Termination reason: Time limit
% 4.21/0.92  % (22232)Termination phase: Saturation
% 4.21/0.92  
% 4.21/0.92  % (22232)Memory used [KB]: 14711
% 4.21/0.92  % (22232)Time elapsed: 0.500 s
% 4.21/0.92  % (22232)------------------------------
% 4.21/0.92  % (22232)------------------------------
% 4.21/0.92  % (22257)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.41/0.94  % (22255)Time limit reached!
% 4.41/0.94  % (22255)------------------------------
% 4.41/0.94  % (22255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.94  % (22255)Termination reason: Time limit
% 4.41/0.94  
% 4.41/0.94  % (22255)Memory used [KB]: 1918
% 4.41/0.94  % (22255)Time elapsed: 0.529 s
% 4.41/0.94  % (22255)------------------------------
% 4.41/0.94  % (22255)------------------------------
% 4.41/0.95  % (22240)Time limit reached!
% 4.41/0.95  % (22240)------------------------------
% 4.41/0.95  % (22240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.95  % (22240)Termination reason: Time limit
% 4.41/0.95  
% 4.41/0.95  % (22240)Memory used [KB]: 4861
% 4.41/0.95  % (22240)Time elapsed: 0.501 s
% 4.41/0.95  % (22240)------------------------------
% 4.41/0.95  % (22240)------------------------------
% 4.41/0.95  % (22256)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 5.02/1.04  % (22258)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.02/1.04  % (22233)Time limit reached!
% 5.02/1.04  % (22233)------------------------------
% 5.02/1.04  % (22233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.04  % (22233)Termination reason: Time limit
% 5.02/1.04  
% 5.02/1.04  % (22233)Memory used [KB]: 8699
% 5.02/1.04  % (22233)Time elapsed: 0.628 s
% 5.02/1.04  % (22233)------------------------------
% 5.02/1.04  % (22233)------------------------------
% 5.02/1.08  % (22260)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.02/1.08  % (22259)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.51/1.15  % (22261)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.42/1.21  % (22230)Refutation found. Thanks to Tanya!
% 6.42/1.21  % SZS status Theorem for theBenchmark
% 6.42/1.21  % SZS output start Proof for theBenchmark
% 6.42/1.21  fof(f10132,plain,(
% 6.42/1.21    $false),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f35,f506,f3313,f1606,f47])).
% 6.42/1.21  fof(f47,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f23])).
% 6.42/1.21  fof(f23,plain,(
% 6.42/1.21    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 6.42/1.21    inference(flattening,[],[f22])).
% 6.42/1.21  fof(f22,plain,(
% 6.42/1.21    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 6.42/1.21    inference(ennf_transformation,[],[f11])).
% 6.42/1.21  fof(f11,axiom,(
% 6.42/1.21    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).
% 6.42/1.21  fof(f1606,plain,(
% 6.42/1.21    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f36,f35,f96,f104])).
% 6.42/1.21  fof(f104,plain,(
% 6.42/1.21    ( ! [X6,X7,X5] : (~r1_tarski(k10_relat_1(X5,X6),k10_relat_1(X5,X7)) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | k1_xboole_0 = k10_relat_1(X5,k6_subset_1(X6,X7))) )),
% 6.42/1.21    inference(superposition,[],[f54,f59])).
% 6.42/1.21  fof(f59,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 6.42/1.21    inference(definition_unfolding,[],[f53,f42])).
% 6.42/1.21  fof(f42,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f8])).
% 6.42/1.21  fof(f8,axiom,(
% 6.42/1.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.42/1.21  fof(f53,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f34])).
% 6.42/1.21  fof(f34,plain,(
% 6.42/1.21    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.42/1.21    inference(nnf_transformation,[],[f2])).
% 6.42/1.21  fof(f2,axiom,(
% 6.42/1.21    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 6.42/1.21  fof(f54,plain,(
% 6.42/1.21    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f27])).
% 6.42/1.21  fof(f27,plain,(
% 6.42/1.21    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 6.42/1.21    inference(flattening,[],[f26])).
% 6.42/1.21  fof(f26,plain,(
% 6.42/1.21    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 6.42/1.21    inference(ennf_transformation,[],[f12])).
% 6.42/1.21  fof(f12,axiom,(
% 6.42/1.21    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 6.42/1.21  fof(f96,plain,(
% 6.42/1.21    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f35,f65,f46])).
% 6.42/1.21  fof(f46,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f21])).
% 6.42/1.21  fof(f21,plain,(
% 6.42/1.21    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.42/1.21    inference(flattening,[],[f20])).
% 6.42/1.21  fof(f20,plain,(
% 6.42/1.21    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.42/1.21    inference(ennf_transformation,[],[f14])).
% 6.42/1.21  fof(f14,axiom,(
% 6.42/1.21    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 6.42/1.21  fof(f65,plain,(
% 6.42/1.21    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f35,f45])).
% 6.42/1.21  fof(f45,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f19])).
% 6.42/1.21  fof(f19,plain,(
% 6.42/1.21    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.42/1.21    inference(ennf_transformation,[],[f10])).
% 6.42/1.21  fof(f10,axiom,(
% 6.42/1.21    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 6.42/1.21  fof(f36,plain,(
% 6.42/1.21    v1_funct_1(sK1)),
% 6.42/1.21    inference(cnf_transformation,[],[f31])).
% 6.42/1.21  fof(f31,plain,(
% 6.42/1.21    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 6.42/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f30])).
% 6.42/1.21  fof(f30,plain,(
% 6.42/1.21    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 6.42/1.21    introduced(choice_axiom,[])).
% 6.42/1.21  fof(f18,plain,(
% 6.42/1.21    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.42/1.21    inference(flattening,[],[f17])).
% 6.42/1.21  fof(f17,plain,(
% 6.42/1.21    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 6.42/1.21    inference(ennf_transformation,[],[f16])).
% 6.42/1.21  fof(f16,negated_conjecture,(
% 6.42/1.21    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.42/1.21    inference(negated_conjecture,[],[f15])).
% 6.42/1.21  fof(f15,conjecture,(
% 6.42/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 6.42/1.21  fof(f3313,plain,(
% 6.42/1.21    r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))),
% 6.42/1.21    inference(superposition,[],[f330,f239])).
% 6.42/1.21  fof(f239,plain,(
% 6.42/1.21    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 6.42/1.21    inference(forward_demodulation,[],[f227,f41])).
% 6.42/1.21  fof(f41,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f7])).
% 6.42/1.21  fof(f7,axiom,(
% 6.42/1.21    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.42/1.21  fof(f227,plain,(
% 6.42/1.21    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0))) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f93,f92])).
% 6.42/1.21  fof(f92,plain,(
% 6.42/1.21    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X1,X2)) = X1 | ~r1_tarski(X1,X2)) )),
% 6.42/1.21    inference(forward_demodulation,[],[f87,f56])).
% 6.42/1.21  fof(f56,plain,(
% 6.42/1.21    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 6.42/1.21    inference(definition_unfolding,[],[f39,f42])).
% 6.42/1.21  fof(f39,plain,(
% 6.42/1.21    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.42/1.21    inference(cnf_transformation,[],[f5])).
% 6.42/1.21  fof(f5,axiom,(
% 6.42/1.21    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 6.42/1.21  fof(f87,plain,(
% 6.42/1.21    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X1,X2)) = k6_subset_1(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 6.42/1.21    inference(superposition,[],[f58,f59])).
% 6.42/1.21  fof(f58,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.42/1.21    inference(definition_unfolding,[],[f44,f43,f42,f42])).
% 6.42/1.21  fof(f43,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.42/1.21    inference(cnf_transformation,[],[f9])).
% 6.42/1.21  fof(f9,axiom,(
% 6.42/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.42/1.21  fof(f44,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.42/1.21    inference(cnf_transformation,[],[f6])).
% 6.42/1.21  fof(f6,axiom,(
% 6.42/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.42/1.21  fof(f93,plain,(
% 6.42/1.21    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f35,f36,f48])).
% 6.42/1.21  fof(f48,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f25])).
% 6.42/1.21  fof(f25,plain,(
% 6.42/1.21    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.42/1.21    inference(flattening,[],[f24])).
% 6.42/1.21  fof(f24,plain,(
% 6.42/1.21    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.42/1.21    inference(ennf_transformation,[],[f13])).
% 6.42/1.21  fof(f13,axiom,(
% 6.42/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 6.42/1.21  fof(f330,plain,(
% 6.42/1.21    ( ! [X15] : (r1_tarski(k6_subset_1(sK0,k1_setfam_1(k2_tarski(sK0,X15))),k2_relat_1(sK1))) )),
% 6.42/1.21    inference(superposition,[],[f85,f88])).
% 6.42/1.21  fof(f88,plain,(
% 6.42/1.21    ( ! [X4,X3] : (k1_setfam_1(k2_tarski(X3,k6_subset_1(X3,X4))) = k6_subset_1(X3,k1_setfam_1(k2_tarski(X3,X4)))) )),
% 6.42/1.21    inference(superposition,[],[f58,f58])).
% 6.42/1.21  fof(f85,plain,(
% 6.42/1.21    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK0,X0)),k2_relat_1(sK1))) )),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f57,f37,f55])).
% 6.42/1.21  fof(f55,plain,(
% 6.42/1.21    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f29])).
% 6.42/1.21  fof(f29,plain,(
% 6.42/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.42/1.21    inference(flattening,[],[f28])).
% 6.42/1.21  fof(f28,plain,(
% 6.42/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.42/1.21    inference(ennf_transformation,[],[f4])).
% 6.42/1.21  fof(f4,axiom,(
% 6.42/1.21    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 6.42/1.21  fof(f37,plain,(
% 6.42/1.21    r1_tarski(sK0,k2_relat_1(sK1))),
% 6.42/1.21    inference(cnf_transformation,[],[f31])).
% 6.42/1.21  fof(f57,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 6.42/1.21    inference(definition_unfolding,[],[f40,f43])).
% 6.42/1.21  fof(f40,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f3])).
% 6.42/1.21  fof(f3,axiom,(
% 6.42/1.21    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 6.42/1.21  fof(f506,plain,(
% 6.42/1.21    k1_xboole_0 != k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f159,f60])).
% 6.42/1.21  fof(f60,plain,(
% 6.42/1.21    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 6.42/1.21    inference(definition_unfolding,[],[f52,f42])).
% 6.42/1.21  fof(f52,plain,(
% 6.42/1.21    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.42/1.21    inference(cnf_transformation,[],[f34])).
% 6.42/1.21  fof(f159,plain,(
% 6.42/1.21    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 6.42/1.21    inference(unit_resulting_resolution,[],[f38,f93,f51])).
% 6.42/1.21  fof(f51,plain,(
% 6.42/1.21    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.42/1.21    inference(cnf_transformation,[],[f33])).
% 6.42/1.21  fof(f33,plain,(
% 6.42/1.21    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.42/1.21    inference(flattening,[],[f32])).
% 6.42/1.21  fof(f32,plain,(
% 6.42/1.21    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.42/1.21    inference(nnf_transformation,[],[f1])).
% 6.42/1.21  fof(f1,axiom,(
% 6.42/1.21    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.42/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.42/1.21  fof(f38,plain,(
% 6.42/1.21    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.42/1.21    inference(cnf_transformation,[],[f31])).
% 6.42/1.21  fof(f35,plain,(
% 6.42/1.21    v1_relat_1(sK1)),
% 6.42/1.21    inference(cnf_transformation,[],[f31])).
% 6.42/1.21  % SZS output end Proof for theBenchmark
% 6.42/1.21  % (22230)------------------------------
% 6.42/1.21  % (22230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.42/1.21  % (22230)Termination reason: Refutation
% 6.42/1.21  
% 6.42/1.21  % (22230)Memory used [KB]: 7164
% 6.42/1.21  % (22230)Time elapsed: 0.776 s
% 6.42/1.21  % (22230)------------------------------
% 6.42/1.21  % (22230)------------------------------
% 6.42/1.21  % (22225)Success in time 0.844 s
%------------------------------------------------------------------------------
