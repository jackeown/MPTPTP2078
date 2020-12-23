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
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 423 expanded)
%              Number of leaves         :   10 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  280 (1869 expanded)
%              Number of equality atoms :   86 ( 598 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f979,plain,(
    $false ),
    inference(subsumption_resolution,[],[f978,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f978,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f977,f49])).

fof(f49,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f977,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f966,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f966,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f965,f108])).

fof(f108,plain,(
    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f107,plain,
    ( sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f49,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f965,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f960,f251])).

fof(f251,plain,(
    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f250,f49])).

fof(f250,plain,
    ( sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f249,f46])).

fof(f249,plain,
    ( sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f247,f47])).

fof(f247,plain,
    ( sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f134,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1))
    | sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) ),
    inference(superposition,[],[f132,f108])).

fof(f132,plain,(
    ! [X0] :
      ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f101,f105])).

fof(f105,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f104,f46])).

fof(f104,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f48,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f48,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f960,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    inference(superposition,[],[f255,f780])).

fof(f780,plain,(
    ! [X5] :
      ( k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5))
      | ~ r2_hidden(X5,k1_relat_1(k4_relat_1(sK1))) ) ),
    inference(forward_demodulation,[],[f779,f509])).

fof(f509,plain,(
    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    inference(subsumption_resolution,[],[f506,f46])).

fof(f506,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    inference(resolution,[],[f504,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f504,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f503,f46])).

fof(f503,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f117,plain,(
    ! [X3] :
      ( ~ v1_relat_1(k4_relat_1(sK1))
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X3))
      | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X3)) ) ),
    inference(superposition,[],[f59,f94])).

fof(f94,plain,(
    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f46,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f779,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
      | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5)) ) ),
    inference(forward_demodulation,[],[f778,f105])).

fof(f778,plain,(
    ! [X5] :
      ( k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) ) ),
    inference(forward_demodulation,[],[f777,f105])).

fof(f777,plain,(
    ! [X5] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X5))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) ) ),
    inference(subsumption_resolution,[],[f773,f46])).

fof(f773,plain,(
    ! [X5] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X5))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f227,f47])).

fof(f227,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(k2_funct_1(X3),sK1),X4) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X3),X4))
      | ~ r2_hidden(X4,k1_relat_1(k5_relat_1(k2_funct_1(X3),sK1)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f224,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f224,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(k2_funct_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(k5_relat_1(k2_funct_1(X3),sK1)))
      | k1_funct_1(k5_relat_1(k2_funct_1(X3),sK1),X4) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X3),X4))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f96,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))
      | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f95,f46])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))
      | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) ) ),
    inference(resolution,[],[f47,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f255,plain,(
    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(subsumption_resolution,[],[f252,f108])).

fof(f252,plain,
    ( sK0 != k1_funct_1(sK1,sK3(sK1,sK0))
    | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(backward_demodulation,[],[f145,f251])).

fof(f145,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f144,f105])).

fof(f144,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(forward_demodulation,[],[f45,f105])).

fof(f45,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4281)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (4273)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (4264)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (4256)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4255)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (4252)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (4258)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (4251)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (4262)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (4276)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (4280)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (4254)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (4275)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (4269)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (4269)Refutation not found, incomplete strategy% (4269)------------------------------
% 0.21/0.55  % (4269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4269)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4269)Memory used [KB]: 10618
% 0.21/0.55  % (4269)Time elapsed: 0.138 s
% 0.21/0.55  % (4269)------------------------------
% 0.21/0.55  % (4269)------------------------------
% 0.21/0.55  % (4261)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (4274)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (4277)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (4267)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (4259)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (4266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (4278)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (4271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (4253)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.56  % (4270)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.56  % (4274)Refutation not found, incomplete strategy% (4274)------------------------------
% 1.50/0.56  % (4274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (4274)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (4274)Memory used [KB]: 10746
% 1.50/0.56  % (4274)Time elapsed: 0.055 s
% 1.50/0.56  % (4274)------------------------------
% 1.50/0.56  % (4274)------------------------------
% 1.50/0.56  % (4263)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (4272)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (4257)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.57  % (4265)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.57  % (4260)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.57  % (4279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.58  % (4273)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f979,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(subsumption_resolution,[],[f978,f46])).
% 1.50/0.58  fof(f46,plain,(
% 1.50/0.58    v1_relat_1(sK1)),
% 1.50/0.58    inference(cnf_transformation,[],[f21])).
% 1.50/0.58  fof(f21,plain,(
% 1.50/0.58    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f20])).
% 1.50/0.58  fof(f20,plain,(
% 1.50/0.58    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f19])).
% 1.50/0.58  fof(f19,negated_conjecture,(
% 1.50/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.50/0.58    inference(negated_conjecture,[],[f18])).
% 1.50/0.58  fof(f18,conjecture,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 1.50/0.58  fof(f978,plain,(
% 1.50/0.58    ~v1_relat_1(sK1)),
% 1.50/0.58    inference(subsumption_resolution,[],[f977,f49])).
% 1.50/0.58  fof(f49,plain,(
% 1.50/0.58    r2_hidden(sK0,k2_relat_1(sK1))),
% 1.50/0.58    inference(cnf_transformation,[],[f21])).
% 1.50/0.58  fof(f977,plain,(
% 1.50/0.58    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.50/0.58    inference(superposition,[],[f966,f55])).
% 1.50/0.58  fof(f55,plain,(
% 1.50/0.58    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f25])).
% 1.50/0.58  fof(f25,plain,(
% 1.50/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f5])).
% 1.50/0.58  fof(f5,axiom,(
% 1.50/0.58    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.50/0.58  fof(f966,plain,(
% 1.50/0.58    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 1.50/0.58    inference(subsumption_resolution,[],[f965,f108])).
% 1.50/0.58  fof(f108,plain,(
% 1.50/0.58    sK0 = k1_funct_1(sK1,sK3(sK1,sK0))),
% 1.50/0.58    inference(subsumption_resolution,[],[f107,f46])).
% 1.50/0.58  fof(f107,plain,(
% 1.50/0.58    sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.50/0.58    inference(subsumption_resolution,[],[f106,f47])).
% 1.50/0.58  fof(f47,plain,(
% 1.50/0.58    v1_funct_1(sK1)),
% 1.50/0.58    inference(cnf_transformation,[],[f21])).
% 1.50/0.58  fof(f106,plain,(
% 1.50/0.58    ~v1_funct_1(sK1) | sK0 = k1_funct_1(sK1,sK3(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.50/0.58    inference(resolution,[],[f49,f85])).
% 1.50/0.58  fof(f85,plain,(
% 1.50/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(equality_resolution,[],[f67])).
% 1.50/0.58  fof(f67,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  fof(f35,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f34])).
% 1.50/0.58  fof(f34,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f10])).
% 1.50/0.58  fof(f10,axiom,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.50/0.58  fof(f965,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 1.50/0.58    inference(forward_demodulation,[],[f960,f251])).
% 1.50/0.58  fof(f251,plain,(
% 1.50/0.58    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)),
% 1.50/0.58    inference(subsumption_resolution,[],[f250,f49])).
% 1.50/0.58  fof(f250,plain,(
% 1.50/0.58    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.50/0.58    inference(subsumption_resolution,[],[f249,f46])).
% 1.50/0.58  fof(f249,plain,(
% 1.50/0.58    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.50/0.58    inference(subsumption_resolution,[],[f247,f47])).
% 1.50/0.58  fof(f247,plain,(
% 1.50/0.58    sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.50/0.58    inference(resolution,[],[f134,f86])).
% 1.50/0.58  fof(f86,plain,(
% 1.50/0.58    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.50/0.58    inference(equality_resolution,[],[f66])).
% 1.50/0.58  fof(f66,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  fof(f134,plain,(
% 1.50/0.58    ~r2_hidden(sK3(sK1,sK0),k1_relat_1(sK1)) | sK3(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),sK0)),
% 1.50/0.58    inference(superposition,[],[f132,f108])).
% 1.50/0.58  fof(f132,plain,(
% 1.50/0.58    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f101,f105])).
% 1.50/0.58  fof(f105,plain,(
% 1.50/0.58    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.50/0.58    inference(subsumption_resolution,[],[f104,f46])).
% 1.50/0.58  fof(f104,plain,(
% 1.50/0.58    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.50/0.58    inference(subsumption_resolution,[],[f99,f47])).
% 1.50/0.58  fof(f99,plain,(
% 1.50/0.58    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.50/0.58    inference(resolution,[],[f48,f62])).
% 1.50/0.58  fof(f62,plain,(
% 1.50/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f33])).
% 1.50/0.58  fof(f33,plain,(
% 1.50/0.58    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.50/0.58  fof(f48,plain,(
% 1.50/0.58    v2_funct_1(sK1)),
% 1.50/0.58    inference(cnf_transformation,[],[f21])).
% 1.50/0.58  fof(f101,plain,(
% 1.50/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f100,f46])).
% 1.50/0.58  fof(f100,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f97,f47])).
% 1.50/0.58  fof(f97,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 1.50/0.58    inference(resolution,[],[f48,f70])).
% 1.50/0.58  fof(f70,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 1.50/0.58    inference(cnf_transformation,[],[f39])).
% 1.50/0.58  fof(f39,plain,(
% 1.50/0.58    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f38])).
% 1.50/0.58  fof(f38,plain,(
% 1.50/0.58    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f17])).
% 1.50/0.58  fof(f17,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 1.50/0.58  fof(f960,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 1.50/0.58    inference(superposition,[],[f255,f780])).
% 1.50/0.58  fof(f780,plain,(
% 1.50/0.58    ( ! [X5] : (k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5)) | ~r2_hidden(X5,k1_relat_1(k4_relat_1(sK1)))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f779,f509])).
% 1.50/0.58  fof(f509,plain,(
% 1.50/0.58    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 1.50/0.58    inference(subsumption_resolution,[],[f506,f46])).
% 1.50/0.58  fof(f506,plain,(
% 1.50/0.58    ~v1_relat_1(sK1) | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 1.50/0.58    inference(resolution,[],[f504,f92])).
% 1.50/0.58  fof(f92,plain,(
% 1.50/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.58    inference(equality_resolution,[],[f77])).
% 1.50/0.58  fof(f77,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f2])).
% 1.50/0.58  fof(f2,axiom,(
% 1.50/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.58  fof(f504,plain,(
% 1.50/0.58    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0))) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f503,f46])).
% 1.50/0.58  fof(f503,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) | ~v1_relat_1(sK1)) )),
% 1.50/0.58    inference(resolution,[],[f117,f52])).
% 1.50/0.58  fof(f52,plain,(
% 1.50/0.58    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f22])).
% 1.50/0.58  fof(f22,plain,(
% 1.50/0.58    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f3])).
% 1.50/0.58  fof(f3,axiom,(
% 1.50/0.58    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.50/0.58  fof(f117,plain,(
% 1.50/0.58    ( ! [X3] : (~v1_relat_1(k4_relat_1(sK1)) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X3)) | k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),X3))) )),
% 1.50/0.58    inference(superposition,[],[f59,f94])).
% 1.50/0.58  fof(f94,plain,(
% 1.50/0.58    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))),
% 1.50/0.58    inference(resolution,[],[f46,f56])).
% 1.50/0.58  fof(f56,plain,(
% 1.50/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f25])).
% 1.50/0.58  fof(f59,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f29])).
% 1.50/0.58  fof(f29,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f28])).
% 1.50/0.58  fof(f28,plain,(
% 1.50/0.58    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.50/0.58  fof(f779,plain,(
% 1.50/0.58    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f778,f105])).
% 1.50/0.58  fof(f778,plain,(
% 1.50/0.58    ( ! [X5] : (k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X5)) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f777,f105])).
% 1.50/0.58  fof(f777,plain,(
% 1.50/0.58    ( ! [X5] : (k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X5)) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f773,f46])).
% 1.50/0.58  fof(f773,plain,(
% 1.50/0.58    ( ! [X5] : (k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),X5) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),X5)) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) | ~v1_relat_1(sK1)) )),
% 1.50/0.58    inference(resolution,[],[f227,f47])).
% 1.50/0.58  fof(f227,plain,(
% 1.50/0.58    ( ! [X4,X3] : (~v1_funct_1(X3) | k1_funct_1(k5_relat_1(k2_funct_1(X3),sK1),X4) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X3),X4)) | ~r2_hidden(X4,k1_relat_1(k5_relat_1(k2_funct_1(X3),sK1))) | ~v1_relat_1(X3)) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f224,f60])).
% 1.50/0.58  fof(f60,plain,(
% 1.50/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f31])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f12])).
% 1.50/0.58  fof(f12,axiom,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.50/0.58  fof(f224,plain,(
% 1.50/0.58    ( ! [X4,X3] : (~v1_relat_1(k2_funct_1(X3)) | ~r2_hidden(X4,k1_relat_1(k5_relat_1(k2_funct_1(X3),sK1))) | k1_funct_1(k5_relat_1(k2_funct_1(X3),sK1),X4) = k1_funct_1(sK1,k1_funct_1(k2_funct_1(X3),X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.50/0.58    inference(resolution,[],[f96,f61])).
% 1.50/0.58  fof(f61,plain,(
% 1.50/0.58    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f31])).
% 1.50/0.58  fof(f96,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) )),
% 1.50/0.58    inference(subsumption_resolution,[],[f95,f46])).
% 1.50/0.58  fof(f95,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) )),
% 1.50/0.58    inference(resolution,[],[f47,f76])).
% 1.50/0.58  fof(f76,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f43])).
% 1.50/0.58  fof(f43,plain,(
% 1.50/0.58    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f42])).
% 1.50/0.58  fof(f42,plain,(
% 1.50/0.58    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f15])).
% 1.50/0.58  fof(f15,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 1.50/0.58  fof(f255,plain,(
% 1.50/0.58    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 1.50/0.58    inference(subsumption_resolution,[],[f252,f108])).
% 1.50/0.58  fof(f252,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,sK3(sK1,sK0)) | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 1.50/0.58    inference(backward_demodulation,[],[f145,f251])).
% 1.50/0.58  fof(f145,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 1.50/0.58    inference(forward_demodulation,[],[f144,f105])).
% 1.50/0.58  fof(f144,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 1.50/0.58    inference(forward_demodulation,[],[f45,f105])).
% 1.50/0.58  fof(f45,plain,(
% 1.50/0.58    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 1.50/0.58    inference(cnf_transformation,[],[f21])).
% 1.50/0.58  % SZS output end Proof for theBenchmark
% 1.50/0.58  % (4273)------------------------------
% 1.50/0.58  % (4273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (4273)Termination reason: Refutation
% 1.50/0.58  
% 1.50/0.58  % (4273)Memory used [KB]: 2302
% 1.50/0.58  % (4273)Time elapsed: 0.160 s
% 1.50/0.58  % (4273)------------------------------
% 1.50/0.58  % (4273)------------------------------
% 1.50/0.58  % (4250)Success in time 0.215 s
%------------------------------------------------------------------------------
