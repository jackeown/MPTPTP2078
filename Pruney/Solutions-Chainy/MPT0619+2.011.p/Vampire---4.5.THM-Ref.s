%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  105 (1200 expanded)
%              Number of leaves         :   14 ( 282 expanded)
%              Depth                    :   25
%              Number of atoms          :  289 (4305 expanded)
%              Number of equality atoms :  129 (2044 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(subsumption_resolution,[],[f245,f179])).

fof(f179,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f176])).

fof(f176,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f141,f153])).

fof(f153,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f152,f47])).

fof(f47,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f152,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f150])).

fof(f150,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK0) != X1
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X1) = k2_relat_1(sK1) ) ),
    inference(superposition,[],[f57,f117])).

fof(f117,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK0) = X0 ) ),
    inference(superposition,[],[f108,f98])).

fof(f98,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f97,f79])).

fof(f79,plain,(
    ! [X5] : k11_relat_1(sK1,X5) = k9_relat_1(sK1,k1_tarski(X5)) ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f81,f95])).

fof(f95,plain,(
    sK1 = k7_relat_1(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(sK0),X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(forward_demodulation,[],[f76,f46])).

fof(f46,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f44,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f81,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(resolution,[],[f89,f78])).

fof(f78,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(X4,X3),sK1)
      | ~ r2_hidden(X3,k11_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f141,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f140,f97])).

fof(f140,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f139,f46])).

fof(f139,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k1_relat_1(sK1)
    | k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f94,f95])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))
      | k1_xboole_0 != k9_relat_1(sK1,X0) ) ),
    inference(superposition,[],[f53,f81])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f245,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f154,f232])).

fof(f232,plain,(
    ! [X0] : sK0 = k1_funct_1(sK1,X0) ),
    inference(subsumption_resolution,[],[f230,f75])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | sK0 = k1_funct_1(sK1,X0) ) ),
    inference(backward_demodulation,[],[f199,f220])).

fof(f220,plain,(
    ! [X1] : k1_xboole_0 = k11_relat_1(sK1,X1) ),
    inference(resolution,[],[f218,f182])).

fof(f182,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_xboole_0)
      | k1_xboole_0 = k11_relat_1(sK1,X6) ) ),
    inference(backward_demodulation,[],[f83,f179])).

fof(f83,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_tarski(sK0))
      | k1_xboole_0 = k11_relat_1(sK1,X6) ) ),
    inference(forward_demodulation,[],[f80,f46])).

fof(f80,plain,(
    ! [X6] :
      ( k1_xboole_0 = k11_relat_1(sK1,X6)
      | r2_hidden(X6,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f218,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f215,f156])).

fof(f156,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f98,f153])).

fof(f215,plain,(
    ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f167,f78])).

fof(f167,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1) ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(k4_tarski(sK0,X0),sK1) ) ),
    inference(backward_demodulation,[],[f106,f153])).

fof(f106,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK1) ) ),
    inference(resolution,[],[f88,f102])).

fof(f102,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 != k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f101,f46])).

fof(f101,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f54,f98])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_tarski(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(forward_demodulation,[],[f87,f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k11_relat_1(sK1,X0))
      | sK0 = k1_funct_1(sK1,X0) ) ),
    inference(superposition,[],[f134,f179])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k11_relat_1(sK1,X1))
      | k1_funct_1(sK1,X1) = X0 ) ),
    inference(superposition,[],[f113,f59])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f113,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k2_tarski(X5,X6),k11_relat_1(sK1,X4))
      | k1_funct_1(sK1,X4) = X5 ) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f154,plain,(
    k1_xboole_0 != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f47,f153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.52  % (26083)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.52  % (26082)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.52  % (26085)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (26098)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.53  % (26089)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.53  % (26097)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.53  % (26090)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.54  % (26087)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.54  % (26088)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.54  % (26095)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.54  % (26100)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.54  % (26080)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % (26094)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (26106)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (26098)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f246,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(subsumption_resolution,[],[f245,f179])).
% 0.23/0.55  fof(f179,plain,(
% 0.23/0.55    k1_xboole_0 = k1_tarski(sK0)),
% 0.23/0.55    inference(trivial_inequality_removal,[],[f176])).
% 0.23/0.55  fof(f176,plain,(
% 0.23/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK0)),
% 0.23/0.55    inference(superposition,[],[f141,f153])).
% 0.23/0.55  fof(f153,plain,(
% 0.23/0.55    k1_xboole_0 = k2_relat_1(sK1)),
% 0.23/0.55    inference(subsumption_resolution,[],[f152,f47])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.23/0.55    inference(flattening,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.23/0.55    inference(ennf_transformation,[],[f18])).
% 0.23/0.55  fof(f18,negated_conjecture,(
% 0.23/0.55    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.23/0.55    inference(negated_conjecture,[],[f17])).
% 0.23/0.55  fof(f17,conjecture,(
% 0.23/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.23/0.55  fof(f152,plain,(
% 0.23/0.55    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.23/0.55    inference(equality_resolution,[],[f150])).
% 0.23/0.55  fof(f150,plain,(
% 0.23/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f149])).
% 0.23/0.55  fof(f149,plain,(
% 0.23/0.55    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1) | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X1) = k2_relat_1(sK1)) )),
% 0.23/0.55    inference(superposition,[],[f57,f117])).
% 0.23/0.55  fof(f117,plain,(
% 0.23/0.55    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 0.23/0.55    inference(resolution,[],[f115,f56])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f38])).
% 0.23/0.55  fof(f38,plain,(
% 0.23/0.55    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f37])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,axiom,(
% 0.23/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.23/0.55  fof(f115,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X0) )),
% 0.23/0.55    inference(superposition,[],[f108,f98])).
% 0.23/0.55  fof(f98,plain,(
% 0.23/0.55    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.23/0.55    inference(superposition,[],[f97,f79])).
% 0.23/0.55  fof(f79,plain,(
% 0.23/0.55    ( ! [X5] : (k11_relat_1(sK1,X5) = k9_relat_1(sK1,k1_tarski(X5))) )),
% 0.23/0.55    inference(resolution,[],[f44,f58])).
% 0.23/0.55  fof(f58,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    v1_relat_1(sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f97,plain,(
% 0.23/0.55    k2_relat_1(sK1) = k9_relat_1(sK1,k1_tarski(sK0))),
% 0.23/0.55    inference(superposition,[],[f81,f95])).
% 0.23/0.55  fof(f95,plain,(
% 0.23/0.55    sK1 = k7_relat_1(sK1,k1_tarski(sK0))),
% 0.23/0.55    inference(resolution,[],[f82,f75])).
% 0.23/0.55  fof(f75,plain,(
% 0.23/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.55    inference(equality_resolution,[],[f67])).
% 0.23/0.55  fof(f67,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f43])).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(flattening,[],[f42])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.55  fof(f82,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0) | sK1 = k7_relat_1(sK1,X0)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f76,f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f76,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | sK1 = k7_relat_1(sK1,X0)) )),
% 0.23/0.55    inference(resolution,[],[f44,f65])).
% 0.23/0.55  fof(f65,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.23/0.55    inference(cnf_transformation,[],[f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(flattening,[],[f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f15])).
% 0.23/0.55  fof(f15,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.23/0.55  fof(f81,plain,(
% 0.23/0.55    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) )),
% 0.23/0.55    inference(resolution,[],[f44,f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f11])).
% 0.23/0.55  fof(f11,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.55  fof(f108,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) )),
% 0.23/0.55    inference(resolution,[],[f89,f78])).
% 0.23/0.55  fof(f78,plain,(
% 0.23/0.55    ( ! [X4,X3] : (r2_hidden(k4_tarski(X4,X3),sK1) | ~r2_hidden(X3,k11_relat_1(sK1,X4))) )),
% 0.23/0.55    inference(resolution,[],[f44,f64])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f41])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.23/0.55    inference(nnf_transformation,[],[f28])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.23/0.55    inference(ennf_transformation,[],[f12])).
% 0.23/0.55  fof(f12,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.23/0.55  fof(f89,plain,(
% 0.23/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f85,f44])).
% 0.23/0.55  fof(f85,plain,(
% 0.23/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3 | ~v1_relat_1(sK1)) )),
% 0.23/0.55    inference(resolution,[],[f45,f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.55    inference(flattening,[],[f33])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.55    inference(nnf_transformation,[],[f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.23/0.55    inference(flattening,[],[f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.23/0.55    inference(ennf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    v1_funct_1(sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f32])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f38])).
% 0.23/0.55  fof(f141,plain,(
% 0.23/0.55    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 0.23/0.55    inference(superposition,[],[f140,f97])).
% 0.23/0.55  fof(f140,plain,(
% 0.23/0.55    k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.23/0.55    inference(forward_demodulation,[],[f139,f46])).
% 0.23/0.55  fof(f139,plain,(
% 0.23/0.55    k1_xboole_0 = k1_relat_1(sK1) | k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0))),
% 0.23/0.55    inference(subsumption_resolution,[],[f138,f44])).
% 0.23/0.55  fof(f138,plain,(
% 0.23/0.55    ~v1_relat_1(sK1) | k1_xboole_0 = k1_relat_1(sK1) | k1_xboole_0 != k9_relat_1(sK1,k1_tarski(sK0))),
% 0.23/0.55    inference(superposition,[],[f94,f95])).
% 0.23/0.55  fof(f94,plain,(
% 0.23/0.55    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) | k1_xboole_0 != k9_relat_1(sK1,X0)) )),
% 0.23/0.55    inference(superposition,[],[f53,f81])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f35])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(nnf_transformation,[],[f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(ennf_transformation,[],[f14])).
% 0.23/0.55  fof(f14,axiom,(
% 0.23/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.23/0.55  fof(f245,plain,(
% 0.23/0.55    k1_xboole_0 != k1_tarski(sK0)),
% 0.23/0.55    inference(backward_demodulation,[],[f154,f232])).
% 0.23/0.55  fof(f232,plain,(
% 0.23/0.55    ( ! [X0] : (sK0 = k1_funct_1(sK1,X0)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f230,f75])).
% 0.23/0.55  fof(f230,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | sK0 = k1_funct_1(sK1,X0)) )),
% 0.23/0.55    inference(backward_demodulation,[],[f199,f220])).
% 0.23/0.55  fof(f220,plain,(
% 0.23/0.55    ( ! [X1] : (k1_xboole_0 = k11_relat_1(sK1,X1)) )),
% 0.23/0.55    inference(resolution,[],[f218,f182])).
% 0.23/0.55  fof(f182,plain,(
% 0.23/0.55    ( ! [X6] : (r2_hidden(X6,k1_xboole_0) | k1_xboole_0 = k11_relat_1(sK1,X6)) )),
% 0.23/0.55    inference(backward_demodulation,[],[f83,f179])).
% 0.23/0.55  fof(f83,plain,(
% 0.23/0.55    ( ! [X6] : (r2_hidden(X6,k1_tarski(sK0)) | k1_xboole_0 = k11_relat_1(sK1,X6)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f80,f46])).
% 0.23/0.55  fof(f80,plain,(
% 0.23/0.55    ( ! [X6] : (k1_xboole_0 = k11_relat_1(sK1,X6) | r2_hidden(X6,k1_relat_1(sK1))) )),
% 0.23/0.55    inference(resolution,[],[f44,f55])).
% 0.23/0.55  fof(f55,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,axiom,(
% 0.23/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.23/0.55  fof(f218,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f215,f156])).
% 0.23/0.55  fof(f156,plain,(
% 0.23/0.55    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.23/0.55    inference(backward_demodulation,[],[f98,f153])).
% 0.23/0.55  fof(f215,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) )),
% 0.23/0.55    inference(resolution,[],[f167,f78])).
% 0.23/0.55  fof(f167,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK1)) )),
% 0.23/0.55    inference(trivial_inequality_removal,[],[f161])).
% 0.23/0.55  fof(f161,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(k4_tarski(sK0,X0),sK1)) )),
% 0.23/0.55    inference(backward_demodulation,[],[f106,f153])).
% 0.23/0.55  fof(f106,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(k4_tarski(sK0,X0),sK1)) )),
% 0.23/0.55    inference(resolution,[],[f88,f102])).
% 0.23/0.55  fof(f102,plain,(
% 0.23/0.55    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 != k2_relat_1(sK1)),
% 0.23/0.55    inference(forward_demodulation,[],[f101,f46])).
% 0.23/0.55  fof(f101,plain,(
% 0.23/0.55    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.23/0.55    inference(subsumption_resolution,[],[f100,f44])).
% 0.23/0.55  fof(f100,plain,(
% 0.23/0.55    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.23/0.55    inference(superposition,[],[f54,f98])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f87,f46])).
% 0.23/0.55  fof(f87,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f84,f44])).
% 0.23/0.55  fof(f84,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.23/0.55    inference(resolution,[],[f45,f48])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f34])).
% 0.23/0.55  fof(f199,plain,(
% 0.23/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k11_relat_1(sK1,X0)) | sK0 = k1_funct_1(sK1,X0)) )),
% 0.23/0.55    inference(superposition,[],[f134,f179])).
% 0.23/0.55  fof(f134,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k11_relat_1(sK1,X1)) | k1_funct_1(sK1,X1) = X0) )),
% 0.23/0.55    inference(superposition,[],[f113,f59])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.55  fof(f113,plain,(
% 0.23/0.55    ( ! [X6,X4,X5] : (~r1_tarski(k2_tarski(X5,X6),k11_relat_1(sK1,X4)) | k1_funct_1(sK1,X4) = X5) )),
% 0.23/0.55    inference(resolution,[],[f108,f60])).
% 0.23/0.55  fof(f60,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f40])).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.23/0.55    inference(flattening,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.23/0.55    inference(nnf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.23/0.55  fof(f154,plain,(
% 0.23/0.55    k1_xboole_0 != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.23/0.55    inference(backward_demodulation,[],[f47,f153])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (26098)------------------------------
% 0.23/0.55  % (26098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (26098)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (26098)Memory used [KB]: 1791
% 0.23/0.55  % (26098)Time elapsed: 0.130 s
% 0.23/0.55  % (26098)------------------------------
% 0.23/0.55  % (26098)------------------------------
% 0.23/0.55  % (26079)Success in time 0.185 s
%------------------------------------------------------------------------------
