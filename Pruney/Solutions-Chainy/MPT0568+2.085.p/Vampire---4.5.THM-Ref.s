%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 109 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   20
%              Number of atoms          :  219 ( 549 expanded)
%              Number of equality atoms :   76 ( 137 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f610])).

fof(f610,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f27,f607])).

fof(f607,plain,(
    ! [X5] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X5) ),
    inference(trivial_inequality_removal,[],[f584])).

fof(f584,plain,(
    ! [X5] :
      ( k10_relat_1(k1_xboole_0,X5) != k10_relat_1(k1_xboole_0,X5)
      | k1_xboole_0 = k10_relat_1(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f190,f582])).

fof(f582,plain,(
    ! [X15,X16] : k10_relat_1(k1_xboole_0,X15) = k4_xboole_0(k10_relat_1(k1_xboole_0,X15),k2_tarski(X16,X16)) ),
    inference(subsumption_resolution,[],[f578,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f578,plain,(
    ! [X15,X16] :
      ( k10_relat_1(k1_xboole_0,X15) = k4_xboole_0(k10_relat_1(k1_xboole_0,X15),k2_tarski(X16,X16))
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1(X16,X15,k1_xboole_0),sK1(X16,X15,k1_xboole_0))) ) ),
    inference(resolution,[],[f572,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f572,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1(X4,X5,k1_xboole_0),k1_xboole_0)
      | k10_relat_1(k1_xboole_0,X5) = k4_xboole_0(k10_relat_1(k1_xboole_0,X5),k2_tarski(X4,X4)) ) ),
    inference(forward_demodulation,[],[f571,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f571,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1(X4,X5,k1_xboole_0),k2_relat_1(k1_xboole_0))
      | k10_relat_1(k1_xboole_0,X5) = k4_xboole_0(k10_relat_1(k1_xboole_0,X5),k2_tarski(X4,X4)) ) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f32,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))
      | k10_relat_1(X2,X1) = k4_xboole_0(k10_relat_1(X2,X1),k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
            & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2)
        & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

% (24285)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f190,plain,(
    ! [X5] :
      ( k4_xboole_0(X5,k2_tarski(sK2(X5,X5,X5),sK2(X5,X5,X5))) != X5
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,X0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f169,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | r2_hidden(sK2(X0,X1,X0),X0) ) ),
    inference(factoring,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f169,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(subsumption_resolution,[],[f163,f30])).

fof(f163,plain,(
    ! [X7] :
      ( k1_xboole_0 = k4_xboole_0(X7,X7)
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK2(X7,X7,k1_xboole_0),sK2(X7,X7,k1_xboole_0))) ) ),
    inference(resolution,[],[f157,f49])).

fof(f157,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,X0,k1_xboole_0),k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X0,X0,k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f140,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,k1_xboole_0),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | r2_hidden(sK2(X0,X1,k1_xboole_0),X0)
      | r2_hidden(sK2(X0,X1,k1_xboole_0),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f136,f45])).

fof(f136,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(sK2(X15,X16,X14),k1_xboole_0)
      | k4_xboole_0(X15,X16) = X14
      | r2_hidden(sK2(X15,X16,X14),X15) ) ),
    inference(superposition,[],[f87,f30])).

fof(f87,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(sK2(X7,X8,X9),k4_xboole_0(X10,X9))
      | k4_xboole_0(X7,X8) = X9
      | r2_hidden(sK2(X7,X8,X9),X7) ) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f27,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:02:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (24280)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24299)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (24287)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (24287)Refutation not found, incomplete strategy% (24287)------------------------------
% 0.22/0.55  % (24287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24291)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (24299)Refutation not found, incomplete strategy% (24299)------------------------------
% 0.22/0.55  % (24299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24299)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24299)Memory used [KB]: 10618
% 0.22/0.55  % (24299)Time elapsed: 0.126 s
% 0.22/0.55  % (24299)------------------------------
% 0.22/0.55  % (24299)------------------------------
% 0.22/0.55  % (24287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24287)Memory used [KB]: 10618
% 0.22/0.55  % (24287)Time elapsed: 0.122 s
% 0.22/0.55  % (24287)------------------------------
% 0.22/0.55  % (24287)------------------------------
% 0.22/0.56  % (24279)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (24279)Refutation not found, incomplete strategy% (24279)------------------------------
% 0.22/0.56  % (24279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24279)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (24279)Memory used [KB]: 10618
% 0.22/0.56  % (24279)Time elapsed: 0.130 s
% 0.22/0.56  % (24279)------------------------------
% 0.22/0.56  % (24279)------------------------------
% 0.22/0.56  % (24277)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (24282)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (24296)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (24278)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.58  % (24300)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (24288)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (24277)Refutation not found, incomplete strategy% (24277)------------------------------
% 0.22/0.58  % (24277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (24277)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (24277)Memory used [KB]: 1663
% 0.22/0.58  % (24277)Time elapsed: 0.153 s
% 0.22/0.58  % (24277)------------------------------
% 0.22/0.58  % (24277)------------------------------
% 0.22/0.58  % (24300)Refutation not found, incomplete strategy% (24300)------------------------------
% 0.22/0.58  % (24300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (24300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (24300)Memory used [KB]: 1663
% 0.22/0.58  % (24300)Time elapsed: 0.110 s
% 0.22/0.58  % (24300)------------------------------
% 0.22/0.58  % (24300)------------------------------
% 0.22/0.58  % (24283)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (24292)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (24281)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (24284)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.59  % (24294)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.60  % (24294)Refutation not found, incomplete strategy% (24294)------------------------------
% 0.22/0.60  % (24294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (24294)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (24294)Memory used [KB]: 10618
% 0.22/0.60  % (24294)Time elapsed: 0.171 s
% 0.22/0.60  % (24294)------------------------------
% 0.22/0.60  % (24294)------------------------------
% 0.22/0.60  % (24280)Refutation found. Thanks to Tanya!
% 0.22/0.60  % SZS status Theorem for theBenchmark
% 0.22/0.60  % (24306)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (24305)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f614,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(trivial_inequality_removal,[],[f610])).
% 0.22/0.60  fof(f610,plain,(
% 0.22/0.60    k1_xboole_0 != k1_xboole_0),
% 0.22/0.60    inference(superposition,[],[f27,f607])).
% 0.22/0.60  fof(f607,plain,(
% 0.22/0.60    ( ! [X5] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X5)) )),
% 0.22/0.60    inference(trivial_inequality_removal,[],[f584])).
% 0.22/0.60  fof(f584,plain,(
% 0.22/0.60    ( ! [X5] : (k10_relat_1(k1_xboole_0,X5) != k10_relat_1(k1_xboole_0,X5) | k1_xboole_0 = k10_relat_1(k1_xboole_0,X5)) )),
% 0.22/0.60    inference(superposition,[],[f190,f582])).
% 0.22/0.60  fof(f582,plain,(
% 0.22/0.60    ( ! [X15,X16] : (k10_relat_1(k1_xboole_0,X15) = k4_xboole_0(k10_relat_1(k1_xboole_0,X15),k2_tarski(X16,X16))) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f578,f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.60  fof(f578,plain,(
% 0.22/0.60    ( ! [X15,X16] : (k10_relat_1(k1_xboole_0,X15) = k4_xboole_0(k10_relat_1(k1_xboole_0,X15),k2_tarski(X16,X16)) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1(X16,X15,k1_xboole_0),sK1(X16,X15,k1_xboole_0)))) )),
% 0.22/0.60    inference(resolution,[],[f572,f49])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f36,f31])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.60    inference(nnf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.60  fof(f572,plain,(
% 0.22/0.60    ( ! [X4,X5] : (r2_hidden(sK1(X4,X5,k1_xboole_0),k1_xboole_0) | k10_relat_1(k1_xboole_0,X5) = k4_xboole_0(k10_relat_1(k1_xboole_0,X5),k2_tarski(X4,X4))) )),
% 0.22/0.60    inference(forward_demodulation,[],[f571,f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.60    inference(cnf_transformation,[],[f8])).
% 0.22/0.60  fof(f8,axiom,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.60  fof(f571,plain,(
% 0.22/0.60    ( ! [X4,X5] : (r2_hidden(sK1(X4,X5,k1_xboole_0),k2_relat_1(k1_xboole_0)) | k10_relat_1(k1_xboole_0,X5) = k4_xboole_0(k10_relat_1(k1_xboole_0,X5),k2_tarski(X4,X4))) )),
% 0.22/0.60    inference(resolution,[],[f69,f55])).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    v1_relat_1(k1_xboole_0)),
% 0.22/0.60    inference(superposition,[],[f32,f50])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.60    inference(equality_resolution,[],[f35])).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.60    inference(flattening,[],[f15])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.60    inference(nnf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) | k10_relat_1(X2,X1) = k4_xboole_0(k10_relat_1(X2,X1),k2_tarski(X0,X0))) )),
% 0.22/0.60    inference(resolution,[],[f38,f48])).
% 0.22/0.60  fof(f48,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0) )),
% 0.22/0.60    inference(definition_unfolding,[],[f37,f31])).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK1(X0,X1,X2)),X2) & r2_hidden(sK1(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  % (24285)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(rectify,[],[f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(nnf_transformation,[],[f12])).
% 0.22/0.60  fof(f12,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.60    inference(ennf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.60  fof(f190,plain,(
% 0.22/0.60    ( ! [X5] : (k4_xboole_0(X5,k2_tarski(sK2(X5,X5,X5),sK2(X5,X5,X5))) != X5 | k1_xboole_0 = X5) )),
% 0.22/0.60    inference(resolution,[],[f171,f49])).
% 0.22/0.60  fof(f171,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(sK2(X0,X0,X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.60    inference(superposition,[],[f169,f94])).
% 0.22/0.60  fof(f94,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | r2_hidden(sK2(X0,X1,X0),X0)) )),
% 0.22/0.60    inference(factoring,[],[f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.60    inference(rectify,[],[f23])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.60    inference(flattening,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.60    inference(nnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.60  fof(f169,plain,(
% 0.22/0.60    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f163,f30])).
% 0.22/0.60  fof(f163,plain,(
% 0.22/0.60    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK2(X7,X7,k1_xboole_0),sK2(X7,X7,k1_xboole_0)))) )),
% 0.22/0.60    inference(resolution,[],[f157,f49])).
% 0.22/0.60  fof(f157,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(sK2(X0,X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.60    inference(duplicate_literal_removal,[],[f141])).
% 0.22/0.60  fof(f141,plain,(
% 0.22/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0) | r2_hidden(sK2(X0,X0,k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.60    inference(resolution,[],[f140,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f140,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,k1_xboole_0),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.60    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.60  fof(f138,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) | r2_hidden(sK2(X0,X1,k1_xboole_0),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.60    inference(resolution,[],[f136,f45])).
% 0.22/0.60  fof(f136,plain,(
% 0.22/0.60    ( ! [X14,X15,X16] : (~r2_hidden(sK2(X15,X16,X14),k1_xboole_0) | k4_xboole_0(X15,X16) = X14 | r2_hidden(sK2(X15,X16,X14),X15)) )),
% 0.22/0.60    inference(superposition,[],[f87,f30])).
% 0.22/0.60  fof(f87,plain,(
% 0.22/0.60    ( ! [X10,X8,X7,X9] : (~r2_hidden(sK2(X7,X8,X9),k4_xboole_0(X10,X9)) | k4_xboole_0(X7,X8) = X9 | r2_hidden(sK2(X7,X8,X9),X7)) )),
% 0.22/0.60    inference(resolution,[],[f45,f53])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.60    inference(equality_resolution,[],[f43])).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.60    inference(cnf_transformation,[],[f26])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f14])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).
% 0.22/0.60  fof(f13,plain,(
% 0.22/0.60    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f11,plain,(
% 0.22/0.60    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.60    inference(ennf_transformation,[],[f10])).
% 0.22/0.60  fof(f10,negated_conjecture,(
% 0.22/0.60    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.60    inference(negated_conjecture,[],[f9])).
% 0.22/0.60  fof(f9,conjecture,(
% 0.22/0.60    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (24280)------------------------------
% 0.22/0.60  % (24280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (24280)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (24280)Memory used [KB]: 11129
% 0.22/0.60  % (24280)Time elapsed: 0.180 s
% 0.22/0.60  % (24280)------------------------------
% 0.22/0.60  % (24280)------------------------------
% 0.22/0.60  % (24285)Refutation not found, incomplete strategy% (24285)------------------------------
% 0.22/0.60  % (24285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (24285)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (24285)Memory used [KB]: 10618
% 0.22/0.60  % (24285)Time elapsed: 0.173 s
% 0.22/0.60  % (24285)------------------------------
% 0.22/0.60  % (24285)------------------------------
% 0.22/0.60  % (24276)Success in time 0.236 s
%------------------------------------------------------------------------------
