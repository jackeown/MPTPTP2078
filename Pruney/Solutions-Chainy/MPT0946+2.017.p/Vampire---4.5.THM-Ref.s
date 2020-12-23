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
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 (1391 expanded)
%              Number of leaves         :   12 ( 276 expanded)
%              Depth                    :   39
%              Number of atoms          :  306 (4546 expanded)
%              Number of equality atoms :   62 (1065 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(resolution,[],[f202,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f202,plain,(
    ! [X0] : ~ v1_relat_1(X0) ),
    inference(resolution,[],[f201,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_wellord1(X0,X3))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 != X3
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f201,plain,(
    ! [X0] : r2_hidden(sK0,X0) ),
    inference(subsumption_resolution,[],[f198,f194])).

fof(f194,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(resolution,[],[f193,f176])).

fof(f176,plain,(
    ! [X1] :
      ( r2_hidden(sK1,sK0)
      | r1_tarski(sK1,X1) ) ),
    inference(forward_demodulation,[],[f175,f73])).

fof(f73,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f175,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) ) ),
    inference(subsumption_resolution,[],[f171,f36])).

fof(f171,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | ~ v1_relat_1(k1_wellord2(sK0))
      | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) ) ),
    inference(resolution,[],[f169,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(sK1,X0),sK1),k1_wellord2(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f165,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK0)) ) ),
    inference(superposition,[],[f85,f163])).

fof(f163,plain,(
    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f162,f82])).

fof(f82,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f81,f33])).

fof(f33,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f79,f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f162,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f160,f129])).

fof(f129,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f125,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f125,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK0,X1),sK1)
      | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
      | r1_tarski(sK0,X1) ) ),
    inference(forward_demodulation,[],[f118,f73])).

fof(f118,plain,(
    ! [X1] :
      ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
      | r1_tarski(sK0,X1)
      | r2_hidden(sK5(sK0,X1),k3_relat_1(k1_wellord2(sK1))) ) ),
    inference(subsumption_resolution,[],[f113,f36])).

fof(f113,plain,(
    ! [X1] :
      ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
      | r1_tarski(sK0,X1)
      | ~ v1_relat_1(k1_wellord2(sK1))
      | r2_hidden(sK5(sK0,X1),k3_relat_1(k1_wellord2(sK1))) ) ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(sK0,X0),sK0),k1_wellord2(sK1))
      | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f107,f57])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1))
      | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ) ),
    inference(superposition,[],[f85,f102])).

fof(f102,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f99,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f97,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f96,f32])).

fof(f96,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f94,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f93,f46])).

fof(f93,plain,
    ( r2_hidden(sK1,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f88,f35])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X0,sK1)
      | sK1 = X0
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f160,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f159,f97])).

fof(f159,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f158,f32])).

fof(f158,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f135,f102])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f134,f73])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X1))
      | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f62,f36])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f193,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f192,f33])).

fof(f192,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f167,f191])).

fof(f191,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f187,f55])).

fof(f187,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f178,f58])).

fof(f178,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK1,X2),sK0)
      | r1_tarski(sK1,X2) ) ),
    inference(forward_demodulation,[],[f177,f73])).

fof(f177,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | r2_hidden(sK5(sK1,X2),k3_relat_1(k1_wellord2(sK0))) ) ),
    inference(subsumption_resolution,[],[f172,f36])).

fof(f172,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | ~ v1_relat_1(k1_wellord2(sK0))
      | r2_hidden(sK5(sK1,X2),k3_relat_1(k1_wellord2(sK0))) ) ),
    inference(resolution,[],[f169,f59])).

fof(f167,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f164,f35])).

fof(f164,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(superposition,[],[f135,f163])).

fof(f198,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f195,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f195,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f193,f93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31941)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31941)Refutation not found, incomplete strategy% (31941)------------------------------
% 0.21/0.51  % (31941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31959)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (31967)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (31941)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31941)Memory used [KB]: 10746
% 0.21/0.51  % (31941)Time elapsed: 0.083 s
% 0.21/0.51  % (31941)------------------------------
% 0.21/0.51  % (31941)------------------------------
% 0.21/0.51  % (31943)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31967)Refutation not found, incomplete strategy% (31967)------------------------------
% 0.21/0.51  % (31967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31967)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31967)Memory used [KB]: 6268
% 0.21/0.51  % (31967)Time elapsed: 0.104 s
% 0.21/0.51  % (31967)------------------------------
% 0.21/0.51  % (31967)------------------------------
% 0.21/0.51  % (31945)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31951)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31940)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (31970)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (31942)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31952)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (31966)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (31946)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (31944)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31964)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31962)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31954)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (31958)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (31968)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (31955)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (31969)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (31957)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (31971)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (31949)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (31950)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (31948)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (31949)Refutation not found, incomplete strategy% (31949)------------------------------
% 0.21/0.53  % (31949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31949)Memory used [KB]: 10618
% 0.21/0.53  % (31949)Time elapsed: 0.123 s
% 0.21/0.53  % (31949)------------------------------
% 0.21/0.53  % (31949)------------------------------
% 0.21/0.53  % (31939)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (31950)Refutation not found, incomplete strategy% (31950)------------------------------
% 0.21/0.53  % (31950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31950)Memory used [KB]: 10618
% 0.21/0.53  % (31950)Time elapsed: 0.127 s
% 0.21/0.53  % (31950)------------------------------
% 0.21/0.53  % (31950)------------------------------
% 0.21/0.53  % (31960)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (31939)Refutation not found, incomplete strategy% (31939)------------------------------
% 0.21/0.53  % (31939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31939)Memory used [KB]: 1663
% 0.21/0.53  % (31939)Time elapsed: 0.120 s
% 0.21/0.53  % (31939)------------------------------
% 0.21/0.53  % (31939)------------------------------
% 0.21/0.53  % (31948)Refutation not found, incomplete strategy% (31948)------------------------------
% 0.21/0.53  % (31948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31948)Memory used [KB]: 10618
% 0.21/0.53  % (31948)Time elapsed: 0.123 s
% 0.21/0.53  % (31948)------------------------------
% 0.21/0.53  % (31948)------------------------------
% 0.21/0.53  % (31947)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (31953)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (31965)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (31945)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (31943)Refutation not found, incomplete strategy% (31943)------------------------------
% 0.21/0.54  % (31943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31964)Refutation not found, incomplete strategy% (31964)------------------------------
% 0.21/0.54  % (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31968)Refutation not found, incomplete strategy% (31968)------------------------------
% 0.21/0.54  % (31968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31968)Memory used [KB]: 10746
% 0.21/0.54  % (31968)Time elapsed: 0.133 s
% 0.21/0.54  % (31968)------------------------------
% 0.21/0.54  % (31968)------------------------------
% 0.21/0.54  % (31957)Refutation not found, incomplete strategy% (31957)------------------------------
% 0.21/0.54  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31957)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31957)Memory used [KB]: 10618
% 0.21/0.54  % (31957)Time elapsed: 0.132 s
% 0.21/0.54  % (31957)------------------------------
% 0.21/0.54  % (31957)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f202,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f201,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_wellord1(X0,X3)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X3) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 != X3 | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f198,f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f193,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK1,sK0) | r1_tarski(sK1,X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f175,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f65,f36])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK1,X1) | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f171,f36])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(sK1,X1) | ~v1_relat_1(k1_wellord2(sK0)) | r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))) )),
% 0.21/0.54    inference(resolution,[],[f169,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK5(sK1,X0),sK1),k1_wellord2(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f165,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k4_tarski(X0,sK1),k1_wellord2(sK0))) )),
% 0.21/0.54    inference(superposition,[],[f85,f163])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.55    inference(resolution,[],[f81,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.21/0.55    inference(resolution,[],[f79,f36])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.55    inference(resolution,[],[f38,f36])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f161])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(superposition,[],[f160,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f125,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f119,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    ( ! [X1] : (r2_hidden(sK5(sK0,X1),sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f118,f73])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X1] : (sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,X1) | r2_hidden(sK5(sK0,X1),k3_relat_1(k1_wellord2(sK1)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f113,f36])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X1] : (sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,X1) | ~v1_relat_1(k1_wellord2(sK1)) | r2_hidden(sK5(sK0,X1),k3_relat_1(k1_wellord2(sK1)))) )),
% 0.21/0.55    inference(resolution,[],[f110,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(k4_tarski(sK5(sK0,X0),sK0),k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f107,f57])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,sK0),k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)) )),
% 0.21/0.55    inference(superposition,[],[f85,f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f101,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    v3_ordinal1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f99,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    v3_ordinal1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f97,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f96,f32])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f35])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f93,f46])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f88,f35])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | sK1 = X0 | r2_hidden(sK1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f47,f32])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f159,f97])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f158,f32])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(superposition,[],[f135,f102])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f134,f73])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f36])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(resolution,[],[f37,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_wellord1(k1_wellord2(X2),X1)) | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))) )),
% 0.21/0.55    inference(resolution,[],[f62,f36])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f192,f33])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(backward_demodulation,[],[f167,f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f187,f55])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.21/0.55    inference(resolution,[],[f178,f58])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    ( ! [X2] : (r2_hidden(sK5(sK1,X2),sK0) | r1_tarski(sK1,X2)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f177,f73])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(sK1,X2) | r2_hidden(sK5(sK1,X2),k3_relat_1(k1_wellord2(sK0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f172,f36])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ( ! [X2] : (r1_tarski(sK1,X2) | ~v1_relat_1(k1_wellord2(sK0)) | r2_hidden(sK5(sK1,X2),k3_relat_1(k1_wellord2(sK0)))) )),
% 0.21/0.55    inference(resolution,[],[f169,f59])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f164,f35])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.55    inference(superposition,[],[f135,f163])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK0,X0) | ~r1_tarski(sK1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f195,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f193,f93])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (31945)------------------------------
% 0.21/0.55  % (31945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31945)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (31945)Memory used [KB]: 6268
% 0.21/0.55  % (31945)Time elapsed: 0.135 s
% 0.21/0.55  % (31945)------------------------------
% 0.21/0.55  % (31945)------------------------------
% 0.21/0.55  % (31933)Success in time 0.182 s
%------------------------------------------------------------------------------
