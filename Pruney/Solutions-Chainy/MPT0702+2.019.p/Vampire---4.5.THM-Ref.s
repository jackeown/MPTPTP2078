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
% DateTime   : Thu Dec  3 12:54:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 150 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 ( 672 expanded)
%              Number of equality atoms :   38 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f697,plain,(
    $false ),
    inference(subsumption_resolution,[],[f696,f132])).

fof(f132,plain,(
    ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f77,f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    k1_xboole_0 != k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).

% (4330)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f28,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f696,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f695,f195])).

fof(f195,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f190,f61])).

fof(f61,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f95,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f95,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f33,f34,f37,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f37,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f695,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f694,f33])).

fof(f694,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f685,f249])).

fof(f249,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f55,f36,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f53,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f36,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f685,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f45,f216])).

fof(f216,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f215,f33])).

fof(f215,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f214,f34])).

fof(f214,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f207,f37])).

fof(f207,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f75,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f75,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (4342)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.50  % (4359)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.51  % (4332)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (4342)Refutation not found, incomplete strategy% (4342)------------------------------
% 0.19/0.51  % (4342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (4333)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (4350)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.51  % (4342)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (4342)Memory used [KB]: 10618
% 0.19/0.51  % (4342)Time elapsed: 0.103 s
% 0.19/0.51  % (4342)------------------------------
% 0.19/0.51  % (4342)------------------------------
% 0.19/0.52  % (4344)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (4359)Refutation not found, incomplete strategy% (4359)------------------------------
% 0.19/0.52  % (4359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (4359)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (4359)Memory used [KB]: 10746
% 0.19/0.52  % (4359)Time elapsed: 0.114 s
% 0.19/0.52  % (4359)------------------------------
% 0.19/0.52  % (4359)------------------------------
% 0.19/0.52  % (4351)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (4335)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (4352)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (4343)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.53  % (4360)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (4341)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.53  % (4339)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.53  % (4346)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (4334)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (4357)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (4329)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.54  % (4331)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.54  % (4337)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.54  % (4358)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.54  % (4333)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f697,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(subsumption_resolution,[],[f696,f132])).
% 0.19/0.54  fof(f132,plain,(
% 0.19/0.54    ~r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f39,f77,f50])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(flattening,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(nnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.54  fof(f77,plain,(
% 0.19/0.54    k1_xboole_0 != k6_subset_1(sK0,sK1)),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f38,f57])).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f51,f44])).
% 0.19/0.54  fof(f44,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f32])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.54    inference(nnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    ~r1_tarski(sK0,sK1)),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).
% 0.19/0.54  % (4330)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.54    inference(negated_conjecture,[],[f13])).
% 0.19/0.54  fof(f13,conjecture,(
% 0.19/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.19/0.54  fof(f39,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.54  fof(f696,plain,(
% 0.19/0.54    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 0.19/0.54    inference(forward_demodulation,[],[f695,f195])).
% 0.19/0.54  fof(f195,plain,(
% 0.19/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.19/0.54    inference(subsumption_resolution,[],[f190,f61])).
% 0.19/0.54  fof(f61,plain,(
% 0.19/0.54    v1_relat_1(k2_funct_1(sK2))),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f33,f34,f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.54    inference(flattening,[],[f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,axiom,(
% 0.19/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    v1_funct_1(sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    v1_relat_1(sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f190,plain,(
% 0.19/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.19/0.54    inference(superposition,[],[f95,f40])).
% 0.19/0.54  fof(f40,plain,(
% 0.19/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.19/0.54  fof(f95,plain,(
% 0.19/0.54    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)) )),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f33,f34,f37,f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f24])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(flattening,[],[f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.54    inference(ennf_transformation,[],[f12])).
% 0.19/0.54  fof(f12,axiom,(
% 0.19/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    v2_funct_1(sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f695,plain,(
% 0.19/0.54    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))),
% 0.19/0.54    inference(subsumption_resolution,[],[f694,f33])).
% 0.19/0.54  fof(f694,plain,(
% 0.19/0.54    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 0.19/0.54    inference(subsumption_resolution,[],[f685,f249])).
% 0.19/0.54  fof(f249,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2))) )),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f55,f36,f70])).
% 0.19/0.54  fof(f70,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(superposition,[],[f53,f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f25])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f43,f44])).
% 0.19/0.54  fof(f43,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.54  fof(f685,plain,(
% 0.19/0.54    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.19/0.54    inference(superposition,[],[f45,f216])).
% 0.19/0.54  fof(f216,plain,(
% 0.19/0.54    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.19/0.54    inference(subsumption_resolution,[],[f215,f33])).
% 0.19/0.54  fof(f215,plain,(
% 0.19/0.54    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 0.19/0.54    inference(subsumption_resolution,[],[f214,f34])).
% 0.19/0.54  fof(f214,plain,(
% 0.19/0.54    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.54    inference(subsumption_resolution,[],[f207,f37])).
% 0.19/0.54  fof(f207,plain,(
% 0.19/0.54    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.54    inference(superposition,[],[f75,f54])).
% 0.19/0.54  fof(f54,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f27])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.54    inference(flattening,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 0.19/0.54  fof(f75,plain,(
% 0.19/0.54    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.19/0.54    inference(unit_resulting_resolution,[],[f35,f56])).
% 0.19/0.54  fof(f56,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f52,f44])).
% 0.19/0.54  fof(f52,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f32])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f45,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(flattening,[],[f20])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,axiom,(
% 0.19/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (4333)------------------------------
% 0.19/0.54  % (4333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (4333)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (4333)Memory used [KB]: 2046
% 0.19/0.54  % (4333)Time elapsed: 0.145 s
% 0.19/0.54  % (4333)------------------------------
% 0.19/0.54  % (4333)------------------------------
% 0.19/0.54  % (4326)Success in time 0.182 s
%------------------------------------------------------------------------------
