%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 872 expanded)
%              Number of leaves         :   13 ( 247 expanded)
%              Depth                    :   22
%              Number of atoms          :  192 (2120 expanded)
%              Number of equality atoms :   77 ( 714 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(global_subsumption,[],[f475,f649])).

fof(f649,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f646,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f71,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f646,plain,(
    ! [X0] : sK0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f291,f622,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP8(sK7(X0,X1,X2),X1,X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f622,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f516,f571])).

fof(f571,plain,(
    ! [X0] : sK5(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f472,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sK5(k1_tarski(X0),X1) = X0
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f472,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    inference(backward_demodulation,[],[f470,f471])).

fof(f471,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(forward_demodulation,[],[f457,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f457,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(k1_relat_1(sK3(sK1)),X0)) ),
    inference(unit_resulting_resolution,[],[f449,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f449,plain,(
    k1_xboole_0 != k1_relat_1(sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f434,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f434,plain,(
    k1_xboole_0 != k2_relat_1(sK3(sK1)) ),
    inference(backward_demodulation,[],[f345,f431])).

fof(f431,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f263,f430])).

fof(f430,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f426,f89])).

fof(f426,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f291,f124,f58])).

fof(f124,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f28,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f263,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(X2,k1_xboole_0)) = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f60,f88])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f28,f48])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f345,plain,(
    k2_relat_1(sK3(sK1)) != k4_xboole_0(k2_relat_1(sK3(sK1)),k2_relat_1(sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f341,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f341,plain,(
    ~ r1_xboole_0(k2_relat_1(sK3(sK1)),k2_relat_1(sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f86,f249])).

fof(f249,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k2_relat_1(sK3(sK1)))
      | ~ r1_tarski(k2_relat_1(sK3(sK1)),X0) ) ),
    inference(superposition,[],[f206,f48])).

fof(f206,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK3(sK1)),k4_xboole_0(X0,k2_relat_1(sK3(sK1)))) ),
    inference(unit_resulting_resolution,[],[f81,f132,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK3(sK1)),sK0),k4_xboole_0(X0,k2_relat_1(sK3(sK1)))) ),
    inference(unit_resulting_resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f83,plain,(
    ! [X0] : ~ sP8(sK5(k2_relat_1(sK3(sK1)),sK0),k2_relat_1(sK3(sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f81,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f81,plain,(
    r2_hidden(sK5(k2_relat_1(sK3(sK1)),sK0),k2_relat_1(sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f68,f45])).

fof(f68,plain,(
    ~ r1_tarski(k2_relat_1(sK3(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f36,f38,f25])).

fof(f25,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f37,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f470,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(forward_demodulation,[],[f458,f38])).

fof(f458,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(k1_relat_1(sK3(sK1)),X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f38,f449,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f32,f31,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | ~ r1_tarski(k2_relat_1(sK2(X0,X1)),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f516,plain,(
    ! [X0] : ~ r2_hidden(sK5(k1_tarski(X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f472,f46])).

fof(f291,plain,(
    ! [X0,X1] : ~ sP8(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f278,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f278,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f125,f277])).

fof(f277,plain,(
    ! [X5] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5)) ),
    inference(forward_demodulation,[],[f265,f88])).

fof(f265,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(k1_xboole_0,X5)) ),
    inference(superposition,[],[f60,f89])).

fof(f125,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) ),
    inference(unit_resulting_resolution,[],[f71,f62])).

fof(f475,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f464,f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f464,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f449,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (996)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (986)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (977)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (974)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (978)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (973)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1000)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (996)Refutation not found, incomplete strategy% (996)------------------------------
% 0.21/0.54  % (996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (996)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (996)Memory used [KB]: 10746
% 0.21/0.54  % (996)Time elapsed: 0.108 s
% 0.21/0.54  % (996)------------------------------
% 0.21/0.54  % (996)------------------------------
% 0.21/0.54  % (999)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (974)Refutation not found, incomplete strategy% (974)------------------------------
% 0.21/0.54  % (974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (974)Memory used [KB]: 10746
% 0.21/0.54  % (974)Time elapsed: 0.127 s
% 0.21/0.54  % (974)------------------------------
% 0.21/0.54  % (974)------------------------------
% 0.21/0.54  % (1002)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (989)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (989)Refutation not found, incomplete strategy% (989)------------------------------
% 0.21/0.54  % (989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (989)Memory used [KB]: 10618
% 0.21/0.54  % (989)Time elapsed: 0.142 s
% 0.21/0.54  % (989)------------------------------
% 0.21/0.54  % (989)------------------------------
% 0.21/0.54  % (983)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (981)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (994)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (981)Refutation not found, incomplete strategy% (981)------------------------------
% 0.21/0.54  % (981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (988)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (1001)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (984)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (981)Memory used [KB]: 10618
% 0.21/0.55  % (981)Time elapsed: 0.143 s
% 0.21/0.55  % (981)------------------------------
% 0.21/0.55  % (981)------------------------------
% 0.21/0.55  % (982)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (980)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (982)Refutation not found, incomplete strategy% (982)------------------------------
% 0.21/0.55  % (982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (982)Memory used [KB]: 10618
% 0.21/0.55  % (982)Time elapsed: 0.150 s
% 0.21/0.55  % (982)------------------------------
% 0.21/0.55  % (982)------------------------------
% 0.21/0.55  % (980)Refutation not found, incomplete strategy% (980)------------------------------
% 0.21/0.55  % (980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (990)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (972)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (972)Refutation not found, incomplete strategy% (972)------------------------------
% 0.21/0.55  % (972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (980)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (980)Memory used [KB]: 10746
% 0.21/0.55  % (980)Time elapsed: 0.148 s
% 0.21/0.55  % (980)------------------------------
% 0.21/0.55  % (980)------------------------------
% 0.21/0.55  % (972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (972)Memory used [KB]: 1663
% 0.21/0.55  % (972)Time elapsed: 0.147 s
% 0.21/0.55  % (972)------------------------------
% 0.21/0.55  % (972)------------------------------
% 0.21/0.55  % (991)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.56  % (998)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.56  % (997)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.57  % (975)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.57  % (987)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.64/0.58  % (1003)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.58  % (995)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.58  % (985)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.59  % (979)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.64/0.61  % (998)Refutation found. Thanks to Tanya!
% 1.64/0.61  % SZS status Theorem for theBenchmark
% 1.64/0.61  % SZS output start Proof for theBenchmark
% 1.64/0.61  fof(f650,plain,(
% 1.64/0.61    $false),
% 1.64/0.61    inference(global_subsumption,[],[f475,f649])).
% 1.64/0.61  fof(f649,plain,(
% 1.64/0.61    k1_xboole_0 = sK0),
% 1.64/0.61    inference(forward_demodulation,[],[f646,f89])).
% 1.64/0.61  fof(f89,plain,(
% 1.64/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f71,f48])).
% 1.64/0.61  fof(f48,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f8])).
% 1.64/0.61  fof(f8,axiom,(
% 1.64/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.64/0.61  fof(f71,plain,(
% 1.64/0.61    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f28,f43])).
% 1.64/0.61  fof(f43,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f23])).
% 1.64/0.61  fof(f23,plain,(
% 1.64/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.64/0.61    inference(ennf_transformation,[],[f3])).
% 1.64/0.61  fof(f3,axiom,(
% 1.64/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.64/0.61  fof(f28,plain,(
% 1.64/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f7])).
% 1.64/0.61  fof(f7,axiom,(
% 1.64/0.61    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.64/0.61  fof(f646,plain,(
% 1.64/0.61    ( ! [X0] : (sK0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f291,f622,f58])).
% 1.64/0.61  fof(f58,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (sP8(sK7(X0,X1,X2),X1,X0) | r2_hidden(sK7(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.64/0.61    inference(cnf_transformation,[],[f2])).
% 1.64/0.61  fof(f2,axiom,(
% 1.64/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.64/0.61  fof(f622,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.64/0.61    inference(backward_demodulation,[],[f516,f571])).
% 1.64/0.61  fof(f571,plain,(
% 1.64/0.61    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f472,f82])).
% 1.64/0.61  fof(f82,plain,(
% 1.64/0.61    ( ! [X0,X1] : (sK5(k1_tarski(X0),X1) = X0 | r1_tarski(k1_tarski(X0),X1)) )),
% 1.64/0.61    inference(resolution,[],[f45,f63])).
% 1.64/0.61  fof(f63,plain,(
% 1.64/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.64/0.61    inference(equality_resolution,[],[f50])).
% 1.64/0.61  fof(f50,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.64/0.61    inference(cnf_transformation,[],[f9])).
% 1.64/0.61  fof(f9,axiom,(
% 1.64/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.64/0.61  fof(f45,plain,(
% 1.64/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f24,plain,(
% 1.64/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.61    inference(ennf_transformation,[],[f1])).
% 1.64/0.61  fof(f1,axiom,(
% 1.64/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.61  fof(f472,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) )),
% 1.64/0.61    inference(backward_demodulation,[],[f470,f471])).
% 1.64/0.61  fof(f471,plain,(
% 1.64/0.61    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 1.64/0.61    inference(forward_demodulation,[],[f457,f38])).
% 1.64/0.61  fof(f38,plain,(
% 1.64/0.61    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f21,plain,(
% 1.64/0.61    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.64/0.61    inference(ennf_transformation,[],[f12])).
% 1.64/0.61  fof(f12,axiom,(
% 1.64/0.61    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.64/0.61  fof(f457,plain,(
% 1.64/0.61    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(k1_relat_1(sK3(sK1)),X0))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f449,f34])).
% 1.64/0.61  fof(f34,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f20,plain,(
% 1.64/0.61    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.64/0.61    inference(ennf_transformation,[],[f13])).
% 1.64/0.61  fof(f13,axiom,(
% 1.64/0.61    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.64/0.61  fof(f449,plain,(
% 1.64/0.61    k1_xboole_0 != k1_relat_1(sK3(sK1))),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f36,f434,f30])).
% 1.64/0.61  fof(f30,plain,(
% 1.64/0.61    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f19])).
% 1.64/0.61  fof(f19,plain,(
% 1.64/0.61    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f11])).
% 1.64/0.61  fof(f11,axiom,(
% 1.64/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.64/0.61  fof(f434,plain,(
% 1.64/0.61    k1_xboole_0 != k2_relat_1(sK3(sK1))),
% 1.64/0.61    inference(backward_demodulation,[],[f345,f431])).
% 1.64/0.61  fof(f431,plain,(
% 1.64/0.61    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 1.64/0.61    inference(backward_demodulation,[],[f263,f430])).
% 1.64/0.61  fof(f430,plain,(
% 1.64/0.61    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X1,k1_xboole_0))) )),
% 1.64/0.61    inference(forward_demodulation,[],[f426,f89])).
% 1.64/0.61  fof(f426,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k1_setfam_1(k2_tarski(X1,k1_xboole_0))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f291,f124,f58])).
% 1.64/0.61  fof(f124,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f28,f62])).
% 1.64/0.61  fof(f62,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.61    inference(definition_unfolding,[],[f41,f39])).
% 1.64/0.61  fof(f39,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f10])).
% 1.64/0.61  fof(f10,axiom,(
% 1.64/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.64/0.61  fof(f41,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f22])).
% 1.64/0.61  fof(f22,plain,(
% 1.64/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.64/0.61    inference(ennf_transformation,[],[f16])).
% 1.64/0.61  fof(f16,plain,(
% 1.64/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.61    inference(rectify,[],[f4])).
% 1.64/0.61  fof(f4,axiom,(
% 1.64/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.64/0.61  fof(f263,plain,(
% 1.64/0.61    ( ! [X2] : (k1_setfam_1(k2_tarski(X2,k1_xboole_0)) = k4_xboole_0(X2,X2)) )),
% 1.64/0.61    inference(superposition,[],[f60,f88])).
% 1.64/0.61  fof(f88,plain,(
% 1.64/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f28,f48])).
% 1.64/0.61  fof(f60,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.64/0.61    inference(definition_unfolding,[],[f40,f39])).
% 1.64/0.61  fof(f40,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f6])).
% 1.64/0.61  fof(f6,axiom,(
% 1.64/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.64/0.61  fof(f345,plain,(
% 1.64/0.61    k2_relat_1(sK3(sK1)) != k4_xboole_0(k2_relat_1(sK3(sK1)),k2_relat_1(sK3(sK1)))),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f341,f47])).
% 1.64/0.61  fof(f47,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f8])).
% 1.64/0.61  fof(f341,plain,(
% 1.64/0.61    ~r1_xboole_0(k2_relat_1(sK3(sK1)),k2_relat_1(sK3(sK1)))),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f86,f249])).
% 1.64/0.61  fof(f249,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_xboole_0(X0,k2_relat_1(sK3(sK1))) | ~r1_tarski(k2_relat_1(sK3(sK1)),X0)) )),
% 1.64/0.61    inference(superposition,[],[f206,f48])).
% 1.64/0.61  fof(f206,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3(sK1)),k4_xboole_0(X0,k2_relat_1(sK3(sK1))))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f81,f132,f44])).
% 1.64/0.61  fof(f44,plain,(
% 1.64/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f132,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK3(sK1)),sK0),k4_xboole_0(X0,k2_relat_1(sK3(sK1))))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f83,f66])).
% 1.64/0.61  fof(f66,plain,(
% 1.64/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP8(X3,X1,X0)) )),
% 1.64/0.61    inference(equality_resolution,[],[f57])).
% 1.64/0.61  fof(f57,plain,(
% 1.64/0.61    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.64/0.61    inference(cnf_transformation,[],[f2])).
% 1.64/0.61  fof(f83,plain,(
% 1.64/0.61    ( ! [X0] : (~sP8(sK5(k2_relat_1(sK3(sK1)),sK0),k2_relat_1(sK3(sK1)),X0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f81,f55])).
% 1.64/0.61  fof(f55,plain,(
% 1.64/0.61    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f2])).
% 1.64/0.61  fof(f81,plain,(
% 1.64/0.61    r2_hidden(sK5(k2_relat_1(sK3(sK1)),sK0),k2_relat_1(sK3(sK1)))),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f68,f45])).
% 1.64/0.61  fof(f68,plain,(
% 1.64/0.61    ~r1_tarski(k2_relat_1(sK3(sK1)),sK0)),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f37,f36,f38,f25])).
% 1.64/0.61  fof(f25,plain,(
% 1.64/0.61    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f18])).
% 1.64/0.61  fof(f18,plain,(
% 1.64/0.61    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.64/0.61    inference(flattening,[],[f17])).
% 1.64/0.61  fof(f17,plain,(
% 1.64/0.61    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.64/0.61    inference(ennf_transformation,[],[f15])).
% 1.64/0.61  fof(f15,negated_conjecture,(
% 1.64/0.61    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.64/0.61    inference(negated_conjecture,[],[f14])).
% 1.64/0.61  fof(f14,conjecture,(
% 1.64/0.61    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.64/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.64/0.61  fof(f37,plain,(
% 1.64/0.61    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f86,plain,(
% 1.64/0.61    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.64/0.61    inference(duplicate_literal_removal,[],[f85])).
% 1.64/0.61  fof(f85,plain,(
% 1.64/0.61    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.64/0.61    inference(resolution,[],[f46,f45])).
% 1.64/0.61  fof(f46,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f24])).
% 1.64/0.61  fof(f36,plain,(
% 1.64/0.61    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.64/0.61    inference(cnf_transformation,[],[f21])).
% 1.64/0.61  fof(f470,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.64/0.61    inference(forward_demodulation,[],[f458,f38])).
% 1.64/0.61  fof(f458,plain,(
% 1.64/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(k1_relat_1(sK3(sK1)),X0)),sK0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f38,f449,f100])).
% 1.64/0.61  fof(f100,plain,(
% 1.64/0.61    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(global_subsumption,[],[f32,f31,f99])).
% 1.64/0.61  fof(f99,plain,(
% 1.64/0.61    ( ! [X0,X1] : (sK1 != X0 | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | ~r1_tarski(k2_relat_1(sK2(X0,X1)),sK0) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(superposition,[],[f25,f33])).
% 1.64/0.61  fof(f33,plain,(
% 1.64/0.61    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f31,plain,(
% 1.64/0.61    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f32,plain,(
% 1.64/0.61    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.64/0.61    inference(cnf_transformation,[],[f20])).
% 1.64/0.61  fof(f516,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(sK5(k1_tarski(X0),sK0),sK0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f472,f46])).
% 1.64/0.61  fof(f291,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~sP8(X0,X1,k1_xboole_0)) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f278,f54])).
% 1.64/0.61  fof(f54,plain,(
% 1.64/0.61    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.64/0.61    inference(cnf_transformation,[],[f2])).
% 1.64/0.61  fof(f278,plain,(
% 1.64/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.64/0.61    inference(backward_demodulation,[],[f125,f277])).
% 1.64/0.61  fof(f277,plain,(
% 1.64/0.61    ( ! [X5] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X5))) )),
% 1.64/0.61    inference(forward_demodulation,[],[f265,f88])).
% 1.64/0.61  fof(f265,plain,(
% 1.64/0.61    ( ! [X5] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_setfam_1(k2_tarski(k1_xboole_0,X5))) )),
% 1.64/0.61    inference(superposition,[],[f60,f89])).
% 1.64/0.61  fof(f125,plain,(
% 1.64/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))) )),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f71,f62])).
% 1.64/0.61  fof(f475,plain,(
% 1.64/0.61    k1_xboole_0 != sK0),
% 1.64/0.61    inference(unit_resulting_resolution,[],[f464,f26])).
% 1.64/0.61  fof(f26,plain,(
% 1.64/0.61    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.64/0.61    inference(cnf_transformation,[],[f18])).
% 1.64/0.61  fof(f464,plain,(
% 1.64/0.61    k1_xboole_0 != sK1),
% 1.64/0.61    inference(superposition,[],[f449,f38])).
% 1.64/0.61  % SZS output end Proof for theBenchmark
% 1.64/0.61  % (998)------------------------------
% 1.64/0.61  % (998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.61  % (998)Termination reason: Refutation
% 1.64/0.61  
% 1.64/0.61  % (998)Memory used [KB]: 6780
% 1.64/0.61  % (998)Time elapsed: 0.187 s
% 1.64/0.61  % (998)------------------------------
% 1.64/0.61  % (998)------------------------------
% 1.64/0.61  % (971)Success in time 0.245 s
%------------------------------------------------------------------------------
