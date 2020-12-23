%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 (1106 expanded)
%              Number of leaves         :   11 ( 284 expanded)
%              Depth                    :   24
%              Number of atoms          :  186 (4540 expanded)
%              Number of equality atoms :   47 ( 458 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f881,plain,(
    $false ),
    inference(subsumption_resolution,[],[f876,f35])).

fof(f35,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25])).

fof(f25,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f876,plain,(
    r1_tarski(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f866])).

fof(f866,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f40,f805])).

fof(f805,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f804,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f804,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f747,f742])).

fof(f742,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f716,f394])).

fof(f394,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f361,f365])).

fof(f365,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f360,f47])).

fof(f360,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k9_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f326,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f326,plain,(
    r1_tarski(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f229,f177])).

fof(f177,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f94,f65])).

fof(f65,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
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

fof(f32,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ! [X2,X3] : k4_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) = k9_relat_1(sK2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f58,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f58,plain,(
    ! [X0,X1] : k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f56,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f34,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f229,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK2,k1_xboole_0),k9_relat_1(sK2,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[],[f181,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f72,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | k1_xboole_0 = k4_xboole_0(X2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(sK2))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f181,plain,(
    ! [X4,X3] : r1_tarski(k9_relat_1(sK2,k4_xboole_0(X3,X4)),k9_relat_1(sK2,X3)) ),
    inference(superposition,[],[f45,f94])).

fof(f361,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f326,f41])).

fof(f716,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f594,f394])).

fof(f594,plain,(
    ! [X2,X3] : k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f200,f89])).

fof(f89,plain,(
    ! [X2,X3] : k4_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k10_relat_1(sK2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f54,f49])).

fof(f54,plain,(
    ! [X0,X1] : k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f200,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(X4,X5)),k10_relat_1(sK2,X4)) ),
    inference(resolution,[],[f166,f41])).

fof(f166,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,X3)),k10_relat_1(sK2,X2)) ),
    inference(superposition,[],[f45,f89])).

fof(f747,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k10_relat_1(sK2,k1_xboole_0),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f210,f742])).

fof(f210,plain,
    ( k4_xboole_0(sK0,sK1) = k10_relat_1(sK2,k1_xboole_0)
    | ~ r1_tarski(k10_relat_1(sK2,k1_xboole_0),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f195,f44])).

fof(f195,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f192,f45])).

fof(f192,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f74,f177])).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (23310)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (23328)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (23320)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (23312)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (23309)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23327)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (23307)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (23308)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (23319)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (23311)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (23316)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (23323)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (23313)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (23332)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (23318)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (23314)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (23321)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (23324)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (23315)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (23306)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (23334)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (23322)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (23319)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f881,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f876,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 0.21/0.54  fof(f876,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f866])).
% 0.21/0.54  fof(f866,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(superposition,[],[f40,f805])).
% 0.21/0.54  fof(f805,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f804,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f804,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(forward_demodulation,[],[f747,f742])).
% 0.21/0.54  fof(f742,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f716,f394])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f361,f365])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f360,f47])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k9_relat_1(sK2,k1_xboole_0))),
% 0.21/0.54    inference(resolution,[],[f326,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    r1_tarski(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f229,f177])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    k1_xboole_0 = k9_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(superposition,[],[f94,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.54    inference(resolution,[],[f32,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) = k9_relat_1(sK2,k4_xboole_0(X2,X3))) )),
% 0.21/0.54    inference(superposition,[],[f58,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f57,f49])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f56,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f55,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k9_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(resolution,[],[f34,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k1_xboole_0),k9_relat_1(sK2,k4_xboole_0(sK0,X0)))) )),
% 0.21/0.54    inference(superposition,[],[f181,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k1_relat_1(sK2))) )),
% 0.21/0.54    inference(resolution,[],[f72,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_xboole_0 = k4_xboole_0(X2,k1_relat_1(sK2))) )),
% 0.21/0.54    inference(resolution,[],[f62,f41])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f33,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ( ! [X4,X3] : (r1_tarski(k9_relat_1(sK2,k4_xboole_0(X3,X4)),k9_relat_1(sK2,X3))) )),
% 0.21/0.54    inference(superposition,[],[f45,f94])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f326,f41])).
% 0.21/0.54  fof(f716,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 0.21/0.54    inference(superposition,[],[f594,f394])).
% 0.21/0.54  fof(f594,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(X2,X3),X2))) )),
% 0.21/0.54    inference(superposition,[],[f200,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k10_relat_1(sK2,k4_xboole_0(X2,X3))) )),
% 0.21/0.54    inference(superposition,[],[f54,f49])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f53,f49])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f52,f30])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(resolution,[],[f31,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(X4,X5)),k10_relat_1(sK2,X4))) )),
% 0.21/0.54    inference(resolution,[],[f166,f41])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X2,X3)),k10_relat_1(sK2,X2))) )),
% 0.21/0.54    inference(superposition,[],[f45,f89])).
% 0.21/0.54  fof(f747,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~r1_tarski(k10_relat_1(sK2,k1_xboole_0),k4_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(backward_demodulation,[],[f210,f742])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    k4_xboole_0(sK0,sK1) = k10_relat_1(sK2,k1_xboole_0) | ~r1_tarski(k10_relat_1(sK2,k1_xboole_0),k4_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f195,f44])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k1_xboole_0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f192,f45])).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 0.21/0.54    inference(superposition,[],[f74,f177])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f70,f30])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k10_relat_1(sK2,k9_relat_1(sK2,X0))) | ~v1_relat_1(sK2)) )),
% 0.21/0.54    inference(resolution,[],[f62,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23319)------------------------------
% 0.21/0.54  % (23319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23319)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23319)Memory used [KB]: 2174
% 0.21/0.54  % (23319)Time elapsed: 0.144 s
% 0.21/0.54  % (23319)------------------------------
% 0.21/0.54  % (23319)------------------------------
% 0.21/0.54  % (23304)Success in time 0.187 s
%------------------------------------------------------------------------------
