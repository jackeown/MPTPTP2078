%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 473 expanded)
%              Number of leaves         :    8 (  85 expanded)
%              Depth                    :   25
%              Number of atoms          :  248 (1988 expanded)
%              Number of equality atoms :   43 ( 536 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(subsumption_resolution,[],[f267,f96])).

fof(f96,plain,(
    sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f60,f95])).

fof(f95,plain,(
    sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f49,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f94,plain,
    ( sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f91,f57])).

fof(f57,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f53,f56])).

fof(f56,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f53,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f52,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f91,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f74,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK1,sK0),sK0),k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f72,f25])).

fof(f72,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(k1_funct_1(sK1,sK0),sK0),k4_relat_1(sK1)) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f45,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f64,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f62,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0)
    | sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f59,f56])).

fof(f59,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f24,f56])).

fof(f24,plain,
    ( sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f267,plain,(
    sK0 = k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) ),
    inference(forward_demodulation,[],[f266,f95])).

fof(f266,plain,(
    k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f265,f49])).

fof(f265,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f264,f26])).

fof(f264,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f263,f25])).

fof(f263,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f259,f57])).

fof(f259,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f133,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f133,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f131,f28])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f130,f26])).

fof(f130,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f129,f25])).

fof(f129,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f127,f57])).

fof(f127,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)))) ),
    inference(resolution,[],[f99,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

% (315)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f99,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f98,f49])).

fof(f98,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f57])).

fof(f93,plain,
    ( ~ v1_funct_1(k4_relat_1(sK1))
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:57:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (324)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (316)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (319)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (313)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (313)Refutation not found, incomplete strategy% (313)------------------------------
% 0.21/0.50  % (313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (313)Memory used [KB]: 10618
% 0.21/0.50  % (313)Time elapsed: 0.038 s
% 0.21/0.50  % (313)------------------------------
% 0.21/0.50  % (313)------------------------------
% 0.21/0.51  % (327)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (318)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (317)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (321)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (329)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (312)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (329)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (314)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f267,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f60,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f29,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    v1_funct_1(k4_relat_1(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f53,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f55,f25])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f54,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    v1_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.53    inference(resolution,[],[f36,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f52,f25])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f35,f26])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~v1_funct_1(k4_relat_1(sK1)) | sK0 = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f74,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(k1_funct_1(sK1,sK0),sK0),k4_relat_1(sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f72,f25])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(k1_funct_1(sK1,sK0),sK0),k4_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f64,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f45,f29])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1) | k4_relat_1(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f63,f25])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f62,f26])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 0.21/0.53    inference(resolution,[],[f46,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) | sK0 != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f59,f56])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    sK0 != k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f24,f56])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    sK0 = k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f266,f95])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f265,f49])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f264,f26])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f263,f25])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f259,f57])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK1,k4_relat_1(sK1)),sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.53    inference(resolution,[],[f133,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f49])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f28])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f26])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f25])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f57])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,k4_relat_1(sK1))))),
% 0.21/0.53    inference(resolution,[],[f99,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.54  % (315)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f49])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f93,f57])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ~v1_funct_1(k4_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.54    inference(resolution,[],[f74,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (329)------------------------------
% 0.21/0.54  % (329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (329)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (329)Memory used [KB]: 1918
% 0.21/0.54  % (329)Time elapsed: 0.105 s
% 0.21/0.54  % (329)------------------------------
% 0.21/0.54  % (329)------------------------------
% 0.21/0.54  % (323)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (311)Success in time 0.18 s
%------------------------------------------------------------------------------
