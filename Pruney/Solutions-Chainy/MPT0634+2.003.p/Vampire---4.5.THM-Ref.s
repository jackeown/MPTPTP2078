%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:17 EST 2020

% Result     : Theorem 2.68s
% Output     : Refutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 511 expanded)
%              Number of leaves         :   10 ( 147 expanded)
%              Depth                    :   21
%              Number of atoms          :  210 (1158 expanded)
%              Number of equality atoms :   42 ( 399 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1486,plain,(
    $false ),
    inference(global_subsumption,[],[f88,f1459,f1449])).

fof(f1449,plain,(
    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f19,f18,f22,f21,f116,f1443,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2)))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f112,f23])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f34,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( k1_funct_1(k6_relat_1(X0),X2) = X2
      | ~ r2_hidden(X2,X0) ) ),
    inference(global_subsumption,[],[f22,f21,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f1443,plain,(
    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f21,f1433])).

fof(f1433,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f1431])).

fof(f1431,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) ),
    inference(resolution,[],[f120,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f120,plain,
    ( sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f104,f119])).

fof(f119,plain,(
    sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) = k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))) ),
    inference(unit_resulting_resolution,[],[f116,f58])).

fof(f104,plain,
    ( sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_relat_1(sK1)) ),
    inference(global_subsumption,[],[f19,f18,f102])).

fof(f102,plain,
    ( sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f100,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != X0
      | r2_hidden(sK3(sK0,k1_relat_1(sK1),X0),X0)
      | sP4(sK3(sK0,k1_relat_1(sK1),X0),k1_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f57,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP4(sK3(X0,X1,X2),X1,X0) ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f43,f43])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) ),
    inference(definition_unfolding,[],[f20,f44])).

fof(f20,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f116,plain,(
    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f21,f111])).

fof(f111,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) ),
    inference(resolution,[],[f106,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f106,plain,
    ( sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0)) ),
    inference(global_subsumption,[],[f19,f18,f105])).

fof(f105,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)
    | sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f103,f23])).

fof(f103,plain,
    ( sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f100,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f1459,plain,(
    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f116,f1443,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,
    ( ~ r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != X0
      | ~ r2_hidden(sK3(sK0,k1_relat_1(sK1),X0),X0)
      | ~ sP4(sK3(sK0,k1_relat_1(sK1),X0),k1_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f57,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ sP4(sK3(X0,X1,X2),X1,X0) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(sK3(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:31:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (21606)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (21615)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (21605)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (21612)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (21608)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (21629)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (21621)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (21611)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (21628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (21607)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (21621)Refutation not found, incomplete strategy% (21621)------------------------------
% 0.22/0.52  % (21621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21621)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21621)Memory used [KB]: 6268
% 0.22/0.52  % (21621)Time elapsed: 0.076 s
% 0.22/0.52  % (21621)------------------------------
% 0.22/0.52  % (21621)------------------------------
% 0.22/0.52  % (21632)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (21633)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (21619)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (21632)Refutation not found, incomplete strategy% (21632)------------------------------
% 0.22/0.53  % (21632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21632)Memory used [KB]: 6268
% 0.22/0.53  % (21632)Time elapsed: 0.123 s
% 0.22/0.53  % (21632)------------------------------
% 0.22/0.53  % (21632)------------------------------
% 0.22/0.53  % (21607)Refutation not found, incomplete strategy% (21607)------------------------------
% 0.22/0.53  % (21607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21607)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21607)Memory used [KB]: 10618
% 0.22/0.53  % (21607)Time elapsed: 0.118 s
% 0.22/0.53  % (21607)------------------------------
% 0.22/0.53  % (21607)------------------------------
% 0.22/0.53  % (21616)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (21618)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21625)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (21634)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (21624)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (21609)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (21633)Refutation not found, incomplete strategy% (21633)------------------------------
% 0.22/0.53  % (21633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21627)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (21635)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (21628)Refutation not found, incomplete strategy% (21628)------------------------------
% 0.22/0.54  % (21628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21628)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21628)Memory used [KB]: 10746
% 0.22/0.54  % (21628)Time elapsed: 0.118 s
% 0.22/0.54  % (21628)------------------------------
% 0.22/0.54  % (21628)------------------------------
% 0.22/0.54  % (21616)Refutation not found, incomplete strategy% (21616)------------------------------
% 0.22/0.54  % (21616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21616)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21616)Memory used [KB]: 10746
% 0.22/0.54  % (21616)Time elapsed: 0.128 s
% 0.22/0.54  % (21616)------------------------------
% 0.22/0.54  % (21616)------------------------------
% 0.22/0.54  % (21613)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (21623)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (21633)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21633)Memory used [KB]: 10746
% 0.22/0.54  % (21633)Time elapsed: 0.128 s
% 0.22/0.54  % (21633)------------------------------
% 0.22/0.54  % (21633)------------------------------
% 0.22/0.54  % (21623)Refutation not found, incomplete strategy% (21623)------------------------------
% 0.22/0.54  % (21623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21623)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21623)Memory used [KB]: 10618
% 0.22/0.54  % (21623)Time elapsed: 0.138 s
% 0.22/0.54  % (21623)------------------------------
% 0.22/0.54  % (21623)------------------------------
% 0.22/0.54  % (21631)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (21620)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (21626)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (21622)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (21614)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (21614)Refutation not found, incomplete strategy% (21614)------------------------------
% 0.22/0.56  % (21614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21614)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21614)Memory used [KB]: 10618
% 0.22/0.56  % (21614)Time elapsed: 0.149 s
% 0.22/0.56  % (21614)------------------------------
% 0.22/0.56  % (21614)------------------------------
% 0.22/0.56  % (21617)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (21636)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (21626)Refutation not found, incomplete strategy% (21626)------------------------------
% 0.22/0.56  % (21626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21626)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21626)Memory used [KB]: 10874
% 0.22/0.56  % (21626)Time elapsed: 0.156 s
% 0.22/0.56  % (21626)------------------------------
% 0.22/0.56  % (21626)------------------------------
% 2.12/0.65  % (21728)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.65  % (21732)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.12/0.66  % (21737)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.12/0.66  % (21727)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.68  % (21738)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.12/0.69  % (21733)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.12/0.69  % (21734)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.68/0.71  % (21743)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.68/0.71  % (21746)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.68/0.73  % (21631)Refutation found. Thanks to Tanya!
% 2.68/0.73  % SZS status Theorem for theBenchmark
% 2.68/0.75  % SZS output start Proof for theBenchmark
% 2.68/0.75  fof(f1486,plain,(
% 2.68/0.75    $false),
% 2.68/0.75    inference(global_subsumption,[],[f88,f1459,f1449])).
% 2.68/0.75  fof(f1449,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),
% 2.68/0.75    inference(unit_resulting_resolution,[],[f19,f18,f22,f21,f116,f1443,f115])).
% 2.68/0.75  fof(f115,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2))) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~r2_hidden(X1,X0)) )),
% 2.68/0.75    inference(duplicate_literal_removal,[],[f114])).
% 2.68/0.75  fof(f114,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2))) | ~r2_hidden(X1,X0)) )),
% 2.68/0.75    inference(forward_demodulation,[],[f112,f23])).
% 2.68/0.75  fof(f23,plain,(
% 2.68/0.75    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.68/0.75    inference(cnf_transformation,[],[f6])).
% 2.68/0.75  fof(f6,axiom,(
% 2.68/0.75    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.68/0.75  fof(f112,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(X2) | r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X0),X2))) | ~r2_hidden(X1,X0)) )),
% 2.68/0.75    inference(superposition,[],[f34,f58])).
% 2.68/0.75  fof(f58,plain,(
% 2.68/0.75    ( ! [X2,X0] : (k1_funct_1(k6_relat_1(X0),X2) = X2 | ~r2_hidden(X2,X0)) )),
% 2.68/0.75    inference(global_subsumption,[],[f22,f21,f52])).
% 2.68/0.75  fof(f52,plain,(
% 2.68/0.75    ( ! [X2,X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 2.68/0.75    inference(equality_resolution,[],[f30])).
% 2.68/0.75  fof(f30,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,X0) | k1_funct_1(X1,X2) = X2 | k6_relat_1(X0) != X1) )),
% 2.68/0.75    inference(cnf_transformation,[],[f15])).
% 2.68/0.75  fof(f15,plain,(
% 2.68/0.75    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.68/0.75    inference(flattening,[],[f14])).
% 2.68/0.75  fof(f14,plain,(
% 2.68/0.75    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.68/0.75    inference(ennf_transformation,[],[f9])).
% 2.68/0.75  fof(f9,axiom,(
% 2.68/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 2.68/0.75  fof(f34,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 2.68/0.75    inference(cnf_transformation,[],[f17])).
% 2.68/0.75  fof(f17,plain,(
% 2.68/0.75    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.68/0.75    inference(flattening,[],[f16])).
% 2.68/0.75  fof(f16,plain,(
% 2.68/0.75    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.68/0.75    inference(ennf_transformation,[],[f8])).
% 2.68/0.75  fof(f8,axiom,(
% 2.68/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 2.68/0.75  fof(f1443,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))),
% 2.68/0.75    inference(unit_resulting_resolution,[],[f22,f21,f1433])).
% 2.68/0.75  fof(f1433,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0))),
% 2.68/0.75    inference(duplicate_literal_removal,[],[f1431])).
% 2.68/0.75  fof(f1431,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1))),
% 2.68/0.75    inference(resolution,[],[f120,f38])).
% 2.68/0.75  fof(f38,plain,(
% 2.68/0.75    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f1])).
% 2.68/0.75  fof(f1,axiom,(
% 2.68/0.75    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.68/0.75  fof(f120,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0))),
% 2.68/0.75    inference(backward_demodulation,[],[f104,f119])).
% 2.68/0.75  fof(f119,plain,(
% 2.68/0.75    sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) = k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))))),
% 2.68/0.75    inference(unit_resulting_resolution,[],[f116,f58])).
% 2.68/0.75  fof(f104,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | r2_hidden(k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_relat_1(sK1))),
% 2.68/0.75    inference(global_subsumption,[],[f19,f18,f102])).
% 2.68/0.75  fof(f102,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | r2_hidden(k1_funct_1(k6_relat_1(sK0),sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 2.68/0.75    inference(resolution,[],[f100,f33])).
% 2.68/0.75  fof(f33,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f17])).
% 2.68/0.75  fof(f100,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) | sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)),
% 2.68/0.75    inference(equality_resolution,[],[f94])).
% 2.68/0.75  fof(f94,plain,(
% 2.68/0.75    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != X0 | r2_hidden(sK3(sK0,k1_relat_1(sK1),X0),X0) | sP4(sK3(sK0,k1_relat_1(sK1),X0),k1_relat_1(sK1),sK0)) )),
% 2.68/0.75    inference(superposition,[],[f57,f48])).
% 2.68/0.75  fof(f48,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | sP4(sK3(X0,X1,X2),X1,X0)) )),
% 2.68/0.75    inference(definition_unfolding,[],[f41,f44])).
% 2.68/0.75  fof(f44,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.68/0.75    inference(definition_unfolding,[],[f26,f43])).
% 2.68/0.75  fof(f43,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.68/0.75    inference(definition_unfolding,[],[f27,f35])).
% 2.68/0.75  fof(f35,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f4])).
% 2.68/0.75  fof(f4,axiom,(
% 2.68/0.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.68/0.75  fof(f27,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f3])).
% 2.68/0.75  fof(f3,axiom,(
% 2.68/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.68/0.75  fof(f26,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.68/0.75    inference(cnf_transformation,[],[f5])).
% 2.68/0.75  fof(f5,axiom,(
% 2.68/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.68/0.75  fof(f41,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.68/0.75    inference(cnf_transformation,[],[f1])).
% 2.68/0.75  fof(f57,plain,(
% 2.68/0.75    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))),
% 2.68/0.75    inference(backward_demodulation,[],[f45,f46])).
% 2.68/0.75  fof(f46,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.68/0.75    inference(definition_unfolding,[],[f25,f43,f43])).
% 2.68/0.75  fof(f25,plain,(
% 2.68/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f2])).
% 2.68/0.75  fof(f2,axiom,(
% 2.68/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.68/0.75  fof(f45,plain,(
% 2.68/0.75    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))),
% 2.68/0.75    inference(definition_unfolding,[],[f20,f44])).
% 2.68/0.75  fof(f20,plain,(
% 2.68/0.75    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 2.68/0.75    inference(cnf_transformation,[],[f13])).
% 2.68/0.75  fof(f13,plain,(
% 2.68/0.75    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.68/0.75    inference(flattening,[],[f12])).
% 2.68/0.75  fof(f12,plain,(
% 2.68/0.75    ? [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) != k3_xboole_0(k1_relat_1(X1),X0) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.68/0.75    inference(ennf_transformation,[],[f11])).
% 2.68/0.75  fof(f11,negated_conjecture,(
% 2.68/0.75    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.68/0.75    inference(negated_conjecture,[],[f10])).
% 2.68/0.75  fof(f10,conjecture,(
% 2.68/0.75    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).
% 2.68/0.75  fof(f116,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)),
% 2.68/0.75    inference(unit_resulting_resolution,[],[f22,f21,f111])).
% 2.68/0.75  fof(f111,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0))),
% 2.68/0.75    inference(duplicate_literal_removal,[],[f110])).
% 2.68/0.75  fof(f110,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0)),
% 2.68/0.75    inference(resolution,[],[f106,f37])).
% 2.68/0.75  fof(f37,plain,(
% 2.68/0.75    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f1])).
% 2.68/0.75  fof(f106,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0))),
% 2.68/0.75    inference(global_subsumption,[],[f19,f18,f105])).
% 2.68/0.75  fof(f105,plain,(
% 2.68/0.75    r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),sK0) | sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1)),
% 2.68/0.75    inference(forward_demodulation,[],[f103,f23])).
% 2.68/0.75  fof(f103,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k6_relat_1(sK0))) | ~v1_relat_1(sK1)),
% 2.68/0.75    inference(resolution,[],[f100,f32])).
% 2.68/0.75  fof(f32,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X1)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f17])).
% 2.68/0.75  fof(f21,plain,(
% 2.68/0.75    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.68/0.75    inference(cnf_transformation,[],[f7])).
% 2.68/0.75  fof(f7,axiom,(
% 2.68/0.75    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.68/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.68/0.75  fof(f22,plain,(
% 2.68/0.75    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.68/0.75    inference(cnf_transformation,[],[f7])).
% 2.68/0.75  fof(f18,plain,(
% 2.68/0.75    v1_relat_1(sK1)),
% 2.68/0.75    inference(cnf_transformation,[],[f13])).
% 2.68/0.75  fof(f19,plain,(
% 2.68/0.75    v1_funct_1(sK1)),
% 2.68/0.75    inference(cnf_transformation,[],[f13])).
% 2.68/0.75  fof(f1459,plain,(
% 2.68/0.75    sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)),
% 2.68/0.75    inference(unit_resulting_resolution,[],[f116,f1443,f36])).
% 2.68/0.75  fof(f36,plain,(
% 2.68/0.75    ( ! [X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.68/0.75    inference(cnf_transformation,[],[f1])).
% 2.68/0.75  fof(f88,plain,(
% 2.68/0.75    ~r2_hidden(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) | ~sP4(sK3(sK0,k1_relat_1(sK1),k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),k1_relat_1(sK1),sK0)),
% 2.68/0.75    inference(equality_resolution,[],[f83])).
% 2.68/0.75  fof(f83,plain,(
% 2.68/0.75    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != X0 | ~r2_hidden(sK3(sK0,k1_relat_1(sK1),X0),X0) | ~sP4(sK3(sK0,k1_relat_1(sK1),X0),k1_relat_1(sK1),sK0)) )),
% 2.68/0.75    inference(superposition,[],[f57,f47])).
% 2.68/0.75  fof(f47,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~sP4(sK3(X0,X1,X2),X1,X0)) )),
% 2.68/0.75    inference(definition_unfolding,[],[f42,f44])).
% 2.68/0.75  fof(f42,plain,(
% 2.68/0.75    ( ! [X2,X0,X1] : (~sP4(sK3(X0,X1,X2),X1,X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.68/0.75    inference(cnf_transformation,[],[f1])).
% 2.68/0.75  % SZS output end Proof for theBenchmark
% 2.68/0.75  % (21631)------------------------------
% 2.68/0.75  % (21631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.75  % (21631)Termination reason: Refutation
% 2.68/0.75  
% 2.68/0.75  % (21631)Memory used [KB]: 8059
% 2.68/0.75  % (21631)Time elapsed: 0.313 s
% 2.68/0.75  % (21631)------------------------------
% 2.68/0.75  % (21631)------------------------------
% 2.68/0.75  % (21602)Success in time 0.385 s
%------------------------------------------------------------------------------
