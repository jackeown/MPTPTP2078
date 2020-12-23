%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:17 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 666 expanded)
%              Number of leaves         :   11 ( 172 expanded)
%              Depth                    :   37
%              Number of atoms          :  225 (1451 expanded)
%              Number of equality atoms :   49 ( 508 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(subsumption_resolution,[],[f598,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f598,plain,(
    ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f597])).

fof(f597,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f592,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f592,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f64,f578])).

fof(f578,plain,(
    k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f577,f187])).

fof(f187,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f179,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f179,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f178,f25])).

fof(f178,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f148,f37])).

fof(f148,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) ),
    inference(superposition,[],[f89,f145])).

fof(f145,plain,(
    sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(resolution,[],[f140,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f140,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(subsumption_resolution,[],[f139,f25])).

fof(f139,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f127,f37])).

fof(f127,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) ),
    inference(superposition,[],[f64,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(sK1,X0))
      | r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X0))),X0) ) ),
    inference(factoring,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X2))),X2)
      | r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X2))),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0)))
      | r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0)))
      | r2_hidden(X1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f77,f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))
      | r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f76,f30])).

fof(f30,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) ) ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) ) ),
    inference(resolution,[],[f68,f29])).

fof(f29,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) ) ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) ) ),
    inference(resolution,[],[f26,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(k6_relat_1(X0),X1),k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) ) ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(k1_funct_1(k6_relat_1(X0),X1),k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) ) ),
    inference(resolution,[],[f69,f29])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k1_funct_1(X2,X3),k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK1))) ) ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X3),k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK1))) ) ),
    inference(resolution,[],[f26,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f577,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f566,f140])).

fof(f566,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f564,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f564,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f563,f25])).

fof(f563,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f562])).

fof(f562,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f558,f37])).

fof(f558,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(superposition,[],[f64,f555])).

fof(f555,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(resolution,[],[f546,f187])).

fof(f546,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f543,f25])).

fof(f543,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(resolution,[],[f153,f26])).

fof(f153,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) ) ),
    inference(subsumption_resolution,[],[f152,f140])).

fof(f152,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)
      | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) ) ),
    inference(forward_demodulation,[],[f151,f30])).

fof(f151,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) ) ),
    inference(subsumption_resolution,[],[f150,f29])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) ) ),
    inference(subsumption_resolution,[],[f149,f28])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k6_relat_1(sK0))
      | ~ v1_funct_1(k6_relat_1(sK0))
      | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0)))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1))) ) ),
    inference(superposition,[],[f42,f145])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f50,f50])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) ),
    inference(definition_unfolding,[],[f27,f51])).

fof(f27,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (31443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.48  % (31467)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.49  % (31458)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.49  % (31451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (31447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (31440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (31451)Refutation not found, incomplete strategy% (31451)------------------------------
% 0.22/0.51  % (31451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31451)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31451)Memory used [KB]: 10618
% 0.22/0.51  % (31451)Time elapsed: 0.124 s
% 0.22/0.51  % (31451)------------------------------
% 0.22/0.51  % (31451)------------------------------
% 1.27/0.52  % (31440)Refutation not found, incomplete strategy% (31440)------------------------------
% 1.27/0.52  % (31440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (31440)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (31440)Memory used [KB]: 1663
% 1.27/0.52  % (31440)Time elapsed: 0.088 s
% 1.27/0.52  % (31440)------------------------------
% 1.27/0.52  % (31440)------------------------------
% 1.27/0.52  % (31441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.52  % (31446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (31442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % (31461)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.54  % (31460)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.54  % (31469)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.54  % (31454)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.54  % (31463)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.54  % (31466)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.54  % (31444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (31453)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.55  % (31457)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.55  % (31457)Refutation not found, incomplete strategy% (31457)------------------------------
% 1.37/0.55  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (31457)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (31457)Memory used [KB]: 10618
% 1.37/0.55  % (31457)Time elapsed: 0.140 s
% 1.37/0.55  % (31457)------------------------------
% 1.37/0.55  % (31457)------------------------------
% 1.37/0.55  % (31468)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (31448)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (31450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (31450)Refutation not found, incomplete strategy% (31450)------------------------------
% 1.37/0.55  % (31450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (31450)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (31450)Memory used [KB]: 10618
% 1.37/0.55  % (31450)Time elapsed: 0.150 s
% 1.37/0.55  % (31450)------------------------------
% 1.37/0.55  % (31450)------------------------------
% 1.37/0.56  % (31459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.56  % (31465)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.56  % (31445)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.56  % (31456)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.56  % (31449)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.56  % (31452)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.56  % (31449)Refutation not found, incomplete strategy% (31449)------------------------------
% 1.37/0.56  % (31449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (31449)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (31449)Memory used [KB]: 10618
% 1.37/0.56  % (31449)Time elapsed: 0.143 s
% 1.37/0.56  % (31449)------------------------------
% 1.37/0.56  % (31449)------------------------------
% 1.37/0.57  % (31455)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.57  % (31455)Refutation not found, incomplete strategy% (31455)------------------------------
% 1.37/0.57  % (31455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (31455)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (31455)Memory used [KB]: 6268
% 1.37/0.57  % (31455)Time elapsed: 0.147 s
% 1.37/0.57  % (31455)------------------------------
% 1.37/0.57  % (31455)------------------------------
% 1.37/0.57  % (31464)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.57  % (31462)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.57  % (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% 1.37/0.57  % (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (31462)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (31462)Memory used [KB]: 10746
% 1.37/0.58  % (31462)Time elapsed: 0.164 s
% 1.37/0.58  % (31462)------------------------------
% 1.37/0.58  % (31462)------------------------------
% 1.37/0.62  % (31461)Refutation found. Thanks to Tanya!
% 1.37/0.62  % SZS status Theorem for theBenchmark
% 1.37/0.62  % SZS output start Proof for theBenchmark
% 1.37/0.62  fof(f599,plain,(
% 1.37/0.62    $false),
% 1.37/0.62    inference(subsumption_resolution,[],[f598,f25])).
% 1.37/0.62  fof(f25,plain,(
% 1.37/0.62    v1_relat_1(sK1)),
% 1.37/0.62    inference(cnf_transformation,[],[f17])).
% 1.37/0.62  fof(f17,plain,(
% 1.37/0.62    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.37/0.62    inference(flattening,[],[f16])).
% 1.98/0.62  fof(f16,plain,(
% 1.98/0.62    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.98/0.62    inference(ennf_transformation,[],[f15])).
% 1.98/0.62  fof(f15,negated_conjecture,(
% 1.98/0.62    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.98/0.62    inference(negated_conjecture,[],[f14])).
% 1.98/0.62  fof(f14,conjecture,(
% 1.98/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).
% 1.98/0.62  fof(f598,plain,(
% 1.98/0.62    ~v1_relat_1(sK1)),
% 1.98/0.62    inference(trivial_inequality_removal,[],[f597])).
% 1.98/0.62  fof(f597,plain,(
% 1.98/0.62    k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.98/0.62    inference(superposition,[],[f592,f37])).
% 1.98/0.62  fof(f37,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f20])).
% 1.98/0.62  fof(f20,plain,(
% 1.98/0.62    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.98/0.62    inference(ennf_transformation,[],[f10])).
% 1.98/0.62  fof(f10,axiom,(
% 1.98/0.62    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.98/0.62  fof(f592,plain,(
% 1.98/0.62    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.62    inference(backward_demodulation,[],[f64,f578])).
% 1.98/0.62  fof(f578,plain,(
% 1.98/0.62    k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.62    inference(subsumption_resolution,[],[f577,f187])).
% 1.98/0.62  fof(f187,plain,(
% 1.98/0.62    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.62    inference(duplicate_literal_removal,[],[f186])).
% 1.98/0.62  fof(f186,plain,(
% 1.98/0.62    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.62    inference(resolution,[],[f179,f58])).
% 1.98/0.62  fof(f58,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.98/0.62    inference(definition_unfolding,[],[f46,f51])).
% 1.98/0.62  fof(f51,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.98/0.62    inference(definition_unfolding,[],[f34,f50])).
% 1.98/0.62  fof(f50,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f35,f43])).
% 1.98/0.62  fof(f43,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f5])).
% 1.98/0.63  fof(f5,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.63  fof(f35,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f4])).
% 1.98/0.63  fof(f4,axiom,(
% 1.98/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.63  fof(f34,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f6])).
% 1.98/0.63  fof(f6,axiom,(
% 1.98/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.98/0.63  fof(f46,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f1])).
% 1.98/0.63  fof(f1,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.98/0.63  fof(f179,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 1.98/0.63    inference(subsumption_resolution,[],[f178,f25])).
% 1.98/0.63  fof(f178,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.98/0.63    inference(superposition,[],[f148,f37])).
% 1.98/0.63  fof(f148,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1))),
% 1.98/0.63    inference(superposition,[],[f89,f145])).
% 1.98/0.63  fof(f145,plain,(
% 1.98/0.63    sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k1_funct_1(k6_relat_1(sK0),sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))))),
% 1.98/0.63    inference(resolution,[],[f140,f38])).
% 1.98/0.63  fof(f38,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) )),
% 1.98/0.63    inference(cnf_transformation,[],[f21])).
% 1.98/0.63  fof(f21,plain,(
% 1.98/0.63    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 1.98/0.63    inference(ennf_transformation,[],[f13])).
% 1.98/0.63  fof(f13,axiom,(
% 1.98/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 1.98/0.63  fof(f140,plain,(
% 1.98/0.63    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 1.98/0.63    inference(subsumption_resolution,[],[f139,f25])).
% 1.98/0.63  fof(f139,plain,(
% 1.98/0.63    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~v1_relat_1(sK1)),
% 1.98/0.63    inference(trivial_inequality_removal,[],[f138])).
% 1.98/0.63  fof(f138,plain,(
% 1.98/0.63    k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~v1_relat_1(sK1)),
% 1.98/0.63    inference(superposition,[],[f127,f37])).
% 1.98/0.63  fof(f127,plain,(
% 1.98/0.63    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0)),
% 1.98/0.63    inference(superposition,[],[f64,f122])).
% 1.98/0.63  fof(f122,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(sK1,X0)) | r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X0))),X0)) )),
% 1.98/0.63    inference(factoring,[],[f83])).
% 1.98/0.63  fof(f83,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X2))),X2) | r2_hidden(sK2(X0,X1,k1_relat_1(k7_relat_1(sK1,X2))),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(sK1,X2))) )),
% 1.98/0.63    inference(resolution,[],[f82,f59])).
% 1.98/0.63  fof(f59,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.98/0.63    inference(definition_unfolding,[],[f45,f51])).
% 1.98/0.63  fof(f45,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f1])).
% 1.98/0.63  fof(f82,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0))) | r2_hidden(X1,X0)) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f81,f25])).
% 1.98/0.63  fof(f81,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X0))) | r2_hidden(X1,X0) | ~v1_relat_1(sK1)) )),
% 1.98/0.63    inference(superposition,[],[f77,f37])).
% 1.98/0.63  fof(f77,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) | r2_hidden(X1,X0)) )),
% 1.98/0.63    inference(forward_demodulation,[],[f76,f30])).
% 1.98/0.63  fof(f30,plain,(
% 1.98/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.98/0.63    inference(cnf_transformation,[],[f8])).
% 1.98/0.63  fof(f8,axiom,(
% 1.98/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.98/0.63  fof(f76,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f74,f28])).
% 1.98/0.63  fof(f28,plain,(
% 1.98/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f11])).
% 1.98/0.63  fof(f11,axiom,(
% 1.98/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.98/0.63  fof(f74,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))) )),
% 1.98/0.63    inference(resolution,[],[f68,f29])).
% 1.98/0.63  fof(f29,plain,(
% 1.98/0.63    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f11])).
% 1.98/0.63  fof(f68,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f66,f25])).
% 1.98/0.63  fof(f66,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))) )),
% 1.98/0.63    inference(resolution,[],[f26,f40])).
% 1.98/0.63  fof(f40,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f24,plain,(
% 1.98/0.63    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.98/0.63    inference(flattening,[],[f23])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.98/0.63    inference(ennf_transformation,[],[f12])).
% 1.98/0.63  fof(f12,axiom,(
% 1.98/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 1.98/0.63  fof(f26,plain,(
% 1.98/0.63    v1_funct_1(sK1)),
% 1.98/0.63    inference(cnf_transformation,[],[f17])).
% 1.98/0.63  fof(f89,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r2_hidden(k1_funct_1(k6_relat_1(X0),X1),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f87,f28])).
% 1.98/0.63  fof(f87,plain,(
% 1.98/0.63    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r2_hidden(k1_funct_1(k6_relat_1(X0),X1),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)))) )),
% 1.98/0.63    inference(resolution,[],[f69,f29])).
% 1.98/0.63  fof(f69,plain,(
% 1.98/0.63    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k1_funct_1(X2,X3),k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f67,f25])).
% 1.98/0.63  fof(f67,plain,(
% 1.98/0.63    ( ! [X2,X3] : (~v1_relat_1(sK1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X3),k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,sK1)))) )),
% 1.98/0.63    inference(resolution,[],[f26,f41])).
% 1.98/0.63  fof(f41,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f577,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.63    inference(subsumption_resolution,[],[f566,f140])).
% 1.98/0.63  fof(f566,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.98/0.63    inference(resolution,[],[f564,f60])).
% 1.98/0.63  fof(f60,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.98/0.63    inference(definition_unfolding,[],[f44,f51])).
% 1.98/0.63  fof(f44,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f1])).
% 1.98/0.63  fof(f564,plain,(
% 1.98/0.63    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.98/0.63    inference(subsumption_resolution,[],[f563,f25])).
% 1.98/0.63  fof(f563,plain,(
% 1.98/0.63    r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.98/0.63    inference(trivial_inequality_removal,[],[f562])).
% 1.98/0.63  fof(f562,plain,(
% 1.98/0.63    k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.98/0.63    inference(superposition,[],[f558,f37])).
% 1.98/0.63  fof(f558,plain,(
% 1.98/0.63    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 1.98/0.63    inference(superposition,[],[f64,f555])).
% 1.98/0.63  fof(f555,plain,(
% 1.98/0.63    k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,sK0)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 1.98/0.63    inference(resolution,[],[f546,f187])).
% 1.98/0.63  fof(f546,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 1.98/0.63    inference(subsumption_resolution,[],[f543,f25])).
% 1.98/0.63  fof(f543,plain,(
% 1.98/0.63    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 1.98/0.63    inference(resolution,[],[f153,f26])).
% 1.98/0.63  fof(f153,plain,(
% 1.98/0.63    ( ! [X1] : (~v1_funct_1(X1) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f152,f140])).
% 1.98/0.63  fof(f152,plain,(
% 1.98/0.63    ( ! [X1] : (~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),sK0) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))) )),
% 1.98/0.63    inference(forward_demodulation,[],[f151,f30])).
% 1.98/0.63  fof(f151,plain,(
% 1.98/0.63    ( ! [X1] : (~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0))) | ~v1_relat_1(X1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f150,f29])).
% 1.98/0.63  fof(f150,plain,(
% 1.98/0.63    ( ! [X1] : (~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_funct_1(k6_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0))) | ~v1_relat_1(X1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f149,f28])).
% 1.98/0.63  fof(f149,plain,(
% 1.98/0.63    ( ! [X1] : (~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k6_relat_1(sK0))) | ~v1_relat_1(X1) | r2_hidden(sK2(sK0,k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),X1)))) )),
% 1.98/0.63    inference(superposition,[],[f42,f145])).
% 1.98/0.63  fof(f42,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f64,plain,(
% 1.98/0.63    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))),
% 1.98/0.63    inference(forward_demodulation,[],[f52,f53])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f33,f50,f50])).
% 1.98/0.63  fof(f33,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f3])).
% 1.98/0.64  fof(f3,axiom,(
% 1.98/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.98/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.98/0.64  fof(f52,plain,(
% 1.98/0.64    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))),
% 1.98/0.64    inference(definition_unfolding,[],[f27,f51])).
% 1.98/0.64  fof(f27,plain,(
% 1.98/0.64    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 1.98/0.64    inference(cnf_transformation,[],[f17])).
% 1.98/0.64  % SZS output end Proof for theBenchmark
% 1.98/0.64  % (31461)------------------------------
% 1.98/0.64  % (31461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.64  % (31461)Termination reason: Refutation
% 1.98/0.64  
% 1.98/0.64  % (31461)Memory used [KB]: 2174
% 1.98/0.64  % (31461)Time elapsed: 0.169 s
% 1.98/0.64  % (31461)------------------------------
% 1.98/0.64  % (31461)------------------------------
% 1.98/0.64  % (31439)Success in time 0.275 s
%------------------------------------------------------------------------------
