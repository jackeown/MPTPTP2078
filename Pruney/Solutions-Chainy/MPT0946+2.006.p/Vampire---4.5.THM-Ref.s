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
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 (2577 expanded)
%              Number of leaves         :   12 ( 488 expanded)
%              Depth                    :   55
%              Number of atoms          :  354 (8489 expanded)
%              Number of equality atoms :   78 (1680 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f32])).

fof(f32,plain,(
    v3_ordinal1(sK1) ),
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

fof(f193,plain,(
    ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f192,f187])).

fof(f187,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f184,f34])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f182,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f181,f35])).

fof(f35,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f180,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f180,plain,(
    r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f179,f35])).

fof(f179,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f178,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r1_ordinal1(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f178,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f33,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f160,f176])).

fof(f176,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f175,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f175,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f174,f32])).

fof(f174,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f173,f82])).

fof(f82,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f52,f35])).

fof(f173,plain,
    ( r1_ordinal1(sK1,sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f172,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f171,f71])).

fof(f71,plain,(
    ! [X1] :
      ( r2_hidden(sK0,X1)
      | r1_ordinal1(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f40,f35])).

fof(f171,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f170,f138])).

fof(f138,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f137,f33])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f69,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f69,plain,(
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

fof(f170,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f169,f111])).

fof(f111,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f103,f49])).

fof(f103,plain,
    ( r1_tarski(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f102,f49])).

fof(f102,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f101,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f98,f81])).

fof(f98,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f90,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f82,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_ordinal1(sK1,X0)
      | r1_ordinal1(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f169,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f168,f32])).

fof(f168,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(superposition,[],[f144,f167])).

fof(f167,plain,(
    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f166,f122])).

fof(f122,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f121,f34])).

fof(f121,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f119,f55])).

fof(f119,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f118,f32])).

fof(f118,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f117,f82])).

fof(f117,plain,
    ( r1_ordinal1(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f116,f32])).

fof(f116,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f99,f71])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f166,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f165,f35])).

fof(f165,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f164,f81])).

fof(f164,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f163,f35])).

fof(f163,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f162,f70])).

fof(f162,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f161,f33])).

fof(f161,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(superposition,[],[f160,f120])).

fof(f120,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f119,f49])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f143,f65])).

fof(f65,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f142,f36])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f160,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f159,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(superposition,[],[f144,f158])).

fof(f158,plain,(
    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f157,f134])).

fof(f134,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f133,f34])).

fof(f133,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f130,f55])).

fof(f130,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f129,f35])).

fof(f129,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f128,f81])).

fof(f128,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f124,f32])).

fof(f124,plain,
    ( ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f100,f70])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(sK0),X1) = X1 ) ),
    inference(resolution,[],[f41,f35])).

fof(f157,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f156,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f155,f82])).

fof(f155,plain,
    ( r1_ordinal1(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f154,f32])).

fof(f154,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f153,f71])).

fof(f153,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f151,f138])).

fof(f151,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f148,f132])).

fof(f132,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f130,f49])).

fof(f148,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f147,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f144,f131])).

fof(f131,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f130,f122])).

fof(f192,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f191,f82])).

fof(f191,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f190,f32])).

fof(f190,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f186,f71])).

fof(f186,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f185,f138])).

fof(f185,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f169,f183])).

fof(f183,plain,(
    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f182,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.46  % (12331)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.47  % (12323)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.48  % (12331)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (12323)Refutation not found, incomplete strategy% (12323)------------------------------
% 0.22/0.48  % (12323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12323)Memory used [KB]: 10490
% 0.22/0.48  % (12323)Time elapsed: 0.054 s
% 0.22/0.48  % (12323)------------------------------
% 0.22/0.48  % (12323)------------------------------
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f193,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    v3_ordinal1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f192,f187])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f184,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    sK0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.22/0.48    inference(resolution,[],[f182,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v3_ordinal1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f180,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f52,f32])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    r1_ordinal1(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f179,f35])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f178,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK1,X0) | r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f40,f32])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f177,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.48    inference(backward_demodulation,[],[f160,f176])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f175,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f174,f32])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f173,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X1] : (~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(resolution,[],[f52,f35])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    r1_ordinal1(sK1,sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f172,f32])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f171,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(sK0,X1) | r1_ordinal1(X1,sK0) | ~v3_ordinal1(X1)) )),
% 0.22/0.48    inference(resolution,[],[f40,f35])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f170,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.48    inference(resolution,[],[f137,f33])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.22/0.48    inference(resolution,[],[f69,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.48    inference(resolution,[],[f38,f36])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(superposition,[],[f169,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(resolution,[],[f103,f49])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(resolution,[],[f102,f49])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f35])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f98,f81])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f97,f35])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f90,f32])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f82,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (r1_ordinal1(sK1,X0) | r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f50,f32])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f168,f32])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(superposition,[],[f144,f167])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f166,f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f34])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.22/0.48    inference(resolution,[],[f119,f55])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f32])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f117,f82])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    r1_ordinal1(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f116,f32])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f35])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f99,f71])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.22/0.48    inference(resolution,[],[f41,f32])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f165,f35])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f164,f81])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    r1_ordinal1(sK0,sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f163,f35])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f162,f70])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ~r2_hidden(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f161,f33])).
% 0.22/0.48  fof(f161,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(superposition,[],[f160,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(resolution,[],[f119,f49])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f143,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f36])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.48    inference(equality_resolution,[],[f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f142,f36])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f37,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f159,f35])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(superposition,[],[f144,f158])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f157,f134])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f133,f34])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.22/0.48    inference(resolution,[],[f130,f55])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f129,f35])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f128,f81])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    r1_ordinal1(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f35])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f32])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.48    inference(resolution,[],[f100,f70])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(sK0),X1) = X1) )),
% 0.22/0.48    inference(resolution,[],[f41,f35])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f156,f32])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f155,f82])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    r1_ordinal1(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f154,f32])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f153,f71])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f151,f138])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(superposition,[],[f148,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(resolution,[],[f130,f49])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f147,f32])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(superposition,[],[f144,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.48    inference(resolution,[],[f130,f122])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f191,f82])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    r1_ordinal1(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f190,f32])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.48    inference(resolution,[],[f186,f71])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f185,f138])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f169,f183])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.48    inference(resolution,[],[f182,f49])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12331)------------------------------
% 0.22/0.48  % (12331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12331)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12331)Memory used [KB]: 1663
% 0.22/0.48  % (12331)Time elapsed: 0.065 s
% 0.22/0.48  % (12331)------------------------------
% 0.22/0.48  % (12331)------------------------------
% 0.22/0.49  % (12311)Success in time 0.115 s
%------------------------------------------------------------------------------
