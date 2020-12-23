%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 524 expanded)
%              Number of leaves         :   12 (  95 expanded)
%              Depth                    :   27
%              Number of atoms          :  305 (2198 expanded)
%              Number of equality atoms :   65 ( 649 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f332,f328])).

fof(f328,plain,(
    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(subsumption_resolution,[],[f317,f301])).

fof(f301,plain,(
    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f300,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f300,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f298,f39])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f298,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f81,plain,(
    r2_hidden(k4_tarski(sK3(sK1,sK0),sK0),sK1) ),
    inference(resolution,[],[f41,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f41,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f317,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(backward_demodulation,[],[f80,f316])).

fof(f316,plain,(
    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0) ),
    inference(forward_demodulation,[],[f315,f76])).

fof(f76,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f75,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f40,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f315,plain,(
    k1_funct_1(k2_funct_1(sK1),sK0) = sK3(sK1,sK0) ),
    inference(forward_demodulation,[],[f314,f301])).

fof(f314,plain,(
    sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f313,f38])).

fof(f313,plain,
    ( ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f312,f40])).

fof(f312,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f304,f39])).

fof(f304,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0))) ),
    inference(resolution,[],[f299,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f299,plain,(
    r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f295,f38])).

fof(f295,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f81,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f80,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(forward_demodulation,[],[f79,f76])).

fof(f79,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(backward_demodulation,[],[f37,f76])).

fof(f37,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f332,plain,(
    sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f324,f301])).

fof(f324,plain,(
    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(backward_demodulation,[],[f268,f316])).

fof(f268,plain,(
    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f267,f38])).

fof(f267,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f266,f77])).

fof(f77,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f73,f76])).

fof(f73,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f71,f38])).

fof(f71,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f266,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f265,f67])).

fof(f67,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f265,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f258,f39])).

fof(f258,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f197,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f197,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(subsumption_resolution,[],[f196,f41])).

fof(f196,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(forward_demodulation,[],[f195,f68])).

fof(f68,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f38,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f195,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(subsumption_resolution,[],[f194,f38])).

fof(f194,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(subsumption_resolution,[],[f193,f77])).

fof(f193,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(subsumption_resolution,[],[f192,f67])).

fof(f192,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(subsumption_resolution,[],[f187,f39])).

fof(f187,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(k4_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) ),
    inference(resolution,[],[f179,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f179,plain,(
    r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f109,f69])).

fof(f69,plain,(
    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f108,f67])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_relat_1(k4_relat_1(sK1))
      | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f103,f77])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ v1_funct_1(k4_relat_1(sK1))
      | ~ v1_relat_1(k4_relat_1(sK1))
      | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1))) ) ),
    inference(superposition,[],[f51,f68])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:47:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1311)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (1315)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (1322)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (1317)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (1306)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (1327)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (1308)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (1305)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1313)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (1326)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (1304)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (1318)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (1307)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (1310)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (1328)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (1323)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (1320)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (1324)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (1321)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.55  % (1325)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (1314)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (1319)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.56  % (1309)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (1316)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  % (1309)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f333,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f332,f328])).
% 0.22/0.56  fof(f328,plain,(
% 0.22/0.56    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f317,f301])).
% 0.22/0.56  fof(f301,plain,(
% 0.22/0.56    sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f300,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.56  fof(f300,plain,(
% 0.22/0.56    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f298,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    v1_funct_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f298,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.56    inference(resolution,[],[f81,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK3(sK1,sK0),sK0),sK1)),
% 0.22/0.56    inference(resolution,[],[f41,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f317,plain,(
% 0.22/0.56    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f80,f316])).
% 0.22/0.56  fof(f316,plain,(
% 0.22/0.56    k1_funct_1(k4_relat_1(sK1),sK0) = sK3(sK1,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f315,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f75,f38])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f74,f39])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.22/0.56    inference(resolution,[],[f40,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    v2_funct_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    k1_funct_1(k2_funct_1(sK1),sK0) = sK3(sK1,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f314,f301])).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f313,f38])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f312,f40])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f304,f39])).
% 0.22/0.56  fof(f304,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK3(sK1,sK0) = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3(sK1,sK0)))),
% 0.22/0.56    inference(resolution,[],[f299,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.22/0.56  fof(f299,plain,(
% 0.22/0.56    r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f295,f38])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    ~v1_relat_1(sK1) | r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f81,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(forward_demodulation,[],[f79,f76])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.22/0.56    inference(backward_demodulation,[],[f37,f76])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f332,plain,(
% 0.22/0.56    sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f324,f301])).
% 0.22/0.56  fof(f324,plain,(
% 0.22/0.56    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,sK3(sK1,sK0))),
% 0.22/0.56    inference(backward_demodulation,[],[f268,f316])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f267,f38])).
% 0.22/0.56  fof(f267,plain,(
% 0.22/0.56    ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f266,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    v1_funct_1(k4_relat_1(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f73,f76])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f71,f38])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ~v1_relat_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f39,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f265,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    v1_relat_1(k4_relat_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f38,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.56  fof(f265,plain,(
% 0.22/0.56    ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f258,f39])).
% 0.22/0.56  fof(f258,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.22/0.56    inference(resolution,[],[f197,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.22/0.56  fof(f197,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f196,f41])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k2_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(forward_demodulation,[],[f195,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f38,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f194,f38])).
% 0.22/0.56  fof(f194,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f193,f77])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f192,f67])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f187,f39])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))),
% 0.22/0.56    inference(resolution,[],[f179,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f110,f41])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f109,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))),
% 0.22/0.56    inference(resolution,[],[f38,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f67])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f103,f77])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k2_relat_1(k4_relat_1(sK1)))) )),
% 0.22/0.56    inference(superposition,[],[f51,f68])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (1309)------------------------------
% 0.22/0.56  % (1309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1309)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (1309)Memory used [KB]: 6396
% 0.22/0.56  % (1309)Time elapsed: 0.147 s
% 0.22/0.56  % (1309)------------------------------
% 0.22/0.56  % (1309)------------------------------
% 0.22/0.57  % (1312)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.58/0.57  % (1329)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.58/0.58  % (1303)Success in time 0.218 s
%------------------------------------------------------------------------------
