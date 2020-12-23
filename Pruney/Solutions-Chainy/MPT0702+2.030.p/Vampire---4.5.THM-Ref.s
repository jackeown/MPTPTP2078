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
% DateTime   : Thu Dec  3 12:54:16 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 229 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 ( 877 expanded)
%              Number of equality atoms :   39 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(subsumption_resolution,[],[f368,f33])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f23])).

fof(f23,plain,
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

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f368,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f367,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f89,f83])).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
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

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f367,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f366,f339])).

fof(f339,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f327,f94])).

fof(f94,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f42,f83])).

fof(f327,plain,(
    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f326,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f326,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f325,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f325,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f321,f32])).

fof(f32,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f321,plain,
    ( r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f39,f317])).

fof(f317,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f307,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f307,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f168,f69])).

fof(f168,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f167,f28])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f166,f29])).

fof(f166,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f366,plain,(
    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f365,f28])).

fof(f365,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f359,f217])).

fof(f217,plain,(
    ! [X8] : r1_tarski(k6_subset_1(sK0,X8),k1_relat_1(sK2)) ),
    inference(superposition,[],[f177,f57])).

fof(f57,plain,(
    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f177,plain,(
    ! [X6,X7,X5] : r1_tarski(k6_subset_1(X5,X6),k2_xboole_0(X5,X7)) ),
    inference(superposition,[],[f62,f55])).

fof(f55,plain,(
    ! [X2,X1] : k2_xboole_0(k6_subset_1(X1,X2),X1) = X1 ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f62,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f45,f51])).

fof(f359,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f37,f306])).

fof(f306,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f168,f72])).

fof(f72,plain,(
    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.58  % (10023)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.58  % (10021)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.60  % (10040)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.60  % (10032)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.61  % (10036)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.61  % (10029)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.68/0.61  % (10024)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.68/0.62  % (10022)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.68/0.62  % (10047)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.63  % (10042)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.68/0.63  % (10047)Refutation not found, incomplete strategy% (10047)------------------------------
% 1.68/0.63  % (10047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.63  % (10047)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.63  
% 1.68/0.63  % (10047)Memory used [KB]: 1663
% 1.68/0.63  % (10047)Time elapsed: 0.002 s
% 1.68/0.63  % (10047)------------------------------
% 1.68/0.63  % (10047)------------------------------
% 1.68/0.63  % (10033)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.68/0.63  % (10018)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.05/0.63  % (10020)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.05/0.63  % (10039)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.05/0.63  % (10030)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.05/0.63  % (10037)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.05/0.63  % (10028)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.05/0.64  % (10028)Refutation not found, incomplete strategy% (10028)------------------------------
% 2.05/0.64  % (10028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (10028)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.64  
% 2.05/0.64  % (10028)Memory used [KB]: 10746
% 2.05/0.64  % (10028)Time elapsed: 0.189 s
% 2.05/0.64  % (10028)------------------------------
% 2.05/0.64  % (10028)------------------------------
% 2.05/0.64  % (10025)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.05/0.64  % (10034)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.05/0.64  % (10030)Refutation not found, incomplete strategy% (10030)------------------------------
% 2.05/0.64  % (10030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (10030)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.64  
% 2.05/0.64  % (10030)Memory used [KB]: 10618
% 2.05/0.64  % (10030)Time elapsed: 0.205 s
% 2.05/0.64  % (10030)------------------------------
% 2.05/0.64  % (10030)------------------------------
% 2.05/0.64  % (10034)Refutation not found, incomplete strategy% (10034)------------------------------
% 2.05/0.64  % (10034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (10027)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.05/0.64  % (10043)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.05/0.64  % (10024)Refutation found. Thanks to Tanya!
% 2.05/0.64  % SZS status Theorem for theBenchmark
% 2.05/0.64  % (10041)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.05/0.64  % (10035)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.05/0.64  % (10026)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.05/0.64  % (10044)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.05/0.64  % (10045)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.05/0.64  % (10031)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.05/0.64  % (10038)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.05/0.65  % (10019)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 2.05/0.65  % (10019)Refutation not found, incomplete strategy% (10019)------------------------------
% 2.05/0.65  % (10019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.65  % (10019)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.65  
% 2.05/0.65  % (10019)Memory used [KB]: 1663
% 2.05/0.65  % (10019)Time elapsed: 0.199 s
% 2.05/0.65  % (10019)------------------------------
% 2.05/0.65  % (10019)------------------------------
% 2.05/0.65  % (10046)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.05/0.65  % SZS output start Proof for theBenchmark
% 2.05/0.65  fof(f373,plain,(
% 2.05/0.65    $false),
% 2.05/0.65    inference(subsumption_resolution,[],[f368,f33])).
% 2.05/0.65  fof(f33,plain,(
% 2.05/0.65    ~r1_tarski(sK0,sK1)),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f24,plain,(
% 2.05/0.65    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.05/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f23])).
% 2.05/0.65  fof(f23,plain,(
% 2.05/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.05/0.65    introduced(choice_axiom,[])).
% 2.05/0.65  fof(f14,plain,(
% 2.05/0.65    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.05/0.65    inference(flattening,[],[f13])).
% 2.05/0.65  fof(f13,plain,(
% 2.05/0.65    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.05/0.65    inference(ennf_transformation,[],[f12])).
% 2.05/0.65  fof(f12,negated_conjecture,(
% 2.05/0.65    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.05/0.65    inference(negated_conjecture,[],[f11])).
% 2.05/0.65  fof(f11,conjecture,(
% 2.05/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 2.05/0.65  fof(f368,plain,(
% 2.05/0.65    r1_tarski(sK0,sK1)),
% 2.05/0.65    inference(resolution,[],[f367,f99])).
% 2.05/0.65  fof(f99,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(subsumption_resolution,[],[f89,f83])).
% 2.05/0.65  fof(f83,plain,(
% 2.05/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.65    inference(trivial_inequality_removal,[],[f80])).
% 2.05/0.65  fof(f80,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.65    inference(superposition,[],[f50,f47])).
% 2.05/0.65  fof(f47,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f34,f36])).
% 2.05/0.65  fof(f36,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f7])).
% 2.05/0.65  fof(f7,axiom,(
% 2.05/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.05/0.65  fof(f34,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f6])).
% 2.05/0.65  fof(f6,axiom,(
% 2.05/0.65    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 2.05/0.65  fof(f50,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f43,f36])).
% 2.05/0.65  fof(f43,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f27])).
% 2.05/0.65  fof(f27,plain,(
% 2.05/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.05/0.65    inference(nnf_transformation,[],[f2])).
% 2.05/0.65  fof(f2,axiom,(
% 2.05/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.05/0.65  fof(f89,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(extensionality_resolution,[],[f42,f50])).
% 2.05/0.65  fof(f42,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f26])).
% 2.05/0.65  fof(f26,plain,(
% 2.05/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.65    inference(flattening,[],[f25])).
% 2.05/0.65  fof(f25,plain,(
% 2.05/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.65    inference(nnf_transformation,[],[f1])).
% 2.05/0.65  fof(f1,axiom,(
% 2.05/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.65  fof(f367,plain,(
% 2.05/0.65    r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)),
% 2.05/0.65    inference(forward_demodulation,[],[f366,f339])).
% 2.05/0.65  fof(f339,plain,(
% 2.05/0.65    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 2.05/0.65    inference(resolution,[],[f327,f94])).
% 2.05/0.65  fof(f94,plain,(
% 2.05/0.65    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 2.05/0.65    inference(resolution,[],[f42,f83])).
% 2.05/0.65  fof(f327,plain,(
% 2.05/0.65    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0)),
% 2.05/0.65    inference(subsumption_resolution,[],[f326,f28])).
% 2.05/0.65  fof(f28,plain,(
% 2.05/0.65    v1_relat_1(sK2)),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f326,plain,(
% 2.05/0.65    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(sK2)),
% 2.05/0.65    inference(subsumption_resolution,[],[f325,f29])).
% 2.05/0.65  fof(f29,plain,(
% 2.05/0.65    v1_funct_1(sK2)),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f325,plain,(
% 2.05/0.65    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.05/0.65    inference(subsumption_resolution,[],[f321,f32])).
% 2.05/0.65  fof(f32,plain,(
% 2.05/0.65    v2_funct_1(sK2)),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f321,plain,(
% 2.05/0.65    r1_tarski(k10_relat_1(sK2,k1_xboole_0),k1_xboole_0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.05/0.65    inference(superposition,[],[f39,f317])).
% 2.05/0.65  fof(f317,plain,(
% 2.05/0.65    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 2.05/0.65    inference(forward_demodulation,[],[f307,f69])).
% 2.05/0.65  fof(f69,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 2.05/0.65    inference(resolution,[],[f49,f51])).
% 2.05/0.65  fof(f51,plain,(
% 2.05/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.65    inference(equality_resolution,[],[f41])).
% 2.05/0.65  fof(f41,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.05/0.65    inference(cnf_transformation,[],[f26])).
% 2.05/0.65  fof(f49,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f44,f36])).
% 2.05/0.65  fof(f44,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f27])).
% 2.05/0.65  fof(f307,plain,(
% 2.05/0.65    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(X2,X2))) )),
% 2.05/0.65    inference(superposition,[],[f168,f69])).
% 2.05/0.65  fof(f168,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 2.05/0.65    inference(subsumption_resolution,[],[f167,f28])).
% 2.05/0.65  fof(f167,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 2.05/0.65    inference(subsumption_resolution,[],[f166,f29])).
% 2.05/0.65  fof(f166,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 2.05/0.65    inference(resolution,[],[f46,f32])).
% 2.05/0.65  fof(f46,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f22])).
% 2.05/0.65  fof(f22,plain,(
% 2.05/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.05/0.65    inference(flattening,[],[f21])).
% 2.05/0.65  fof(f21,plain,(
% 2.05/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.05/0.65    inference(ennf_transformation,[],[f8])).
% 2.05/0.65  fof(f8,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 2.05/0.65  fof(f39,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f19])).
% 2.05/0.65  fof(f19,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.05/0.65    inference(flattening,[],[f18])).
% 2.05/0.65  fof(f18,plain,(
% 2.05/0.65    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.05/0.65    inference(ennf_transformation,[],[f10])).
% 2.05/0.65  fof(f10,axiom,(
% 2.05/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 2.05/0.65  fof(f366,plain,(
% 2.05/0.65    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))),
% 2.05/0.65    inference(subsumption_resolution,[],[f365,f28])).
% 2.05/0.65  fof(f365,plain,(
% 2.05/0.65    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~v1_relat_1(sK2)),
% 2.05/0.65    inference(subsumption_resolution,[],[f359,f217])).
% 2.05/0.65  fof(f217,plain,(
% 2.05/0.65    ( ! [X8] : (r1_tarski(k6_subset_1(sK0,X8),k1_relat_1(sK2))) )),
% 2.05/0.65    inference(superposition,[],[f177,f57])).
% 2.05/0.65  fof(f57,plain,(
% 2.05/0.65    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2))),
% 2.05/0.65    inference(resolution,[],[f38,f31])).
% 2.05/0.65  fof(f31,plain,(
% 2.05/0.65    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f38,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  fof(f17,plain,(
% 2.05/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f4])).
% 2.05/0.65  fof(f4,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.05/0.65  fof(f177,plain,(
% 2.05/0.65    ( ! [X6,X7,X5] : (r1_tarski(k6_subset_1(X5,X6),k2_xboole_0(X5,X7))) )),
% 2.05/0.65    inference(superposition,[],[f62,f55])).
% 2.05/0.65  fof(f55,plain,(
% 2.05/0.65    ( ! [X2,X1] : (k2_xboole_0(k6_subset_1(X1,X2),X1) = X1) )),
% 2.05/0.65    inference(resolution,[],[f38,f48])).
% 2.05/0.65  fof(f48,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f35,f36])).
% 2.05/0.65  fof(f35,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f5])).
% 2.05/0.65  fof(f5,axiom,(
% 2.05/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.05/0.65  fof(f62,plain,(
% 2.05/0.65    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 2.05/0.65    inference(resolution,[],[f58,f45])).
% 2.05/0.65  fof(f45,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f20])).
% 2.05/0.65  fof(f20,plain,(
% 2.05/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.05/0.65    inference(ennf_transformation,[],[f3])).
% 2.05/0.65  fof(f3,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.05/0.65  fof(f58,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(resolution,[],[f45,f51])).
% 2.05/0.65  fof(f359,plain,(
% 2.05/0.65    r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 2.05/0.65    inference(superposition,[],[f37,f306])).
% 2.05/0.65  fof(f306,plain,(
% 2.05/0.65    k1_xboole_0 = k9_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 2.05/0.65    inference(superposition,[],[f168,f72])).
% 2.05/0.65  fof(f72,plain,(
% 2.05/0.65    k1_xboole_0 = k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.05/0.65    inference(resolution,[],[f49,f30])).
% 2.05/0.65  fof(f30,plain,(
% 2.05/0.65    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 2.05/0.65    inference(cnf_transformation,[],[f24])).
% 2.05/0.65  fof(f37,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f16])).
% 2.05/0.65  fof(f16,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.05/0.65    inference(flattening,[],[f15])).
% 2.05/0.66  fof(f15,plain,(
% 2.05/0.66    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f9])).
% 2.05/0.66  fof(f9,axiom,(
% 2.05/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (10024)------------------------------
% 2.05/0.66  % (10024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (10024)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (10024)Memory used [KB]: 10874
% 2.05/0.66  % (10024)Time elapsed: 0.206 s
% 2.05/0.66  % (10024)------------------------------
% 2.05/0.66  % (10024)------------------------------
% 2.05/0.66  % (10017)Success in time 0.286 s
%------------------------------------------------------------------------------
