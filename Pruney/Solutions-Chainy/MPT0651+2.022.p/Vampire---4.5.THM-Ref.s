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
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 335 expanded)
%              Number of leaves         :   12 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 (1447 expanded)
%              Number of equality atoms :   72 ( 551 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f45])).

fof(f45,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f205,plain,(
    ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f201,f188])).

fof(f188,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f60,f186])).

fof(f186,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f185,f45])).

fof(f185,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f181,f146])).

fof(f146,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f145,f35])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f145,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f144,f28])).

fof(f144,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f143,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0))))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f39,f47])).

fof(f47,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f52,f63])).

fof(f63,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f62,f58])).

fof(f58,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f62,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f61,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f30])).

fof(f55,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f52,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(X4))
      | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f60,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f59,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f31,f58])).

fof(f31,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f201,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f98,f50])).

fof(f50,plain,(
    ! [X2] :
      ( k2_relat_1(k5_relat_1(sK0,X2)) = k9_relat_1(X2,k2_relat_1(sK0))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f98,plain,(
    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f97,f66])).

fof(f66,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f65,f58])).

fof(f65,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f30])).

fof(f56,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f86,f63])).

fof(f86,plain,(
    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.31  % Computer   : n024.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 20:11:36 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.41  % (3637)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.18/0.41  % (3648)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.18/0.41  % (3648)Refutation found. Thanks to Tanya!
% 0.18/0.41  % SZS status Theorem for theBenchmark
% 0.18/0.42  % (3641)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.18/0.42  % (3653)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f206,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(subsumption_resolution,[],[f205,f45])).
% 0.18/0.42  fof(f45,plain,(
% 0.18/0.42    v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(resolution,[],[f28,f36])).
% 0.18/0.42  fof(f36,plain,(
% 0.18/0.42    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f15])).
% 0.18/0.42  fof(f15,plain,(
% 0.18/0.42    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.18/0.42  fof(f28,plain,(
% 0.18/0.42    v1_relat_1(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f27,plain,(
% 0.18/0.42    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).
% 0.18/0.42  fof(f26,plain,(
% 0.18/0.42    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f14,plain,(
% 0.18/0.42    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.18/0.42    inference(flattening,[],[f13])).
% 0.18/0.42  fof(f13,plain,(
% 0.18/0.42    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f12])).
% 0.18/0.42  fof(f12,negated_conjecture,(
% 0.18/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.18/0.42    inference(negated_conjecture,[],[f11])).
% 0.18/0.42  fof(f11,conjecture,(
% 0.18/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.18/0.42  fof(f205,plain,(
% 0.18/0.42    ~v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(subsumption_resolution,[],[f201,f188])).
% 0.18/0.42  fof(f188,plain,(
% 0.18/0.42    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.42    inference(trivial_inequality_removal,[],[f187])).
% 0.18/0.42  fof(f187,plain,(
% 0.18/0.42    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.42    inference(backward_demodulation,[],[f60,f186])).
% 0.18/0.42  fof(f186,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.42    inference(subsumption_resolution,[],[f185,f45])).
% 0.18/0.42  fof(f185,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(subsumption_resolution,[],[f181,f146])).
% 0.18/0.42  fof(f146,plain,(
% 0.18/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.18/0.42    inference(forward_demodulation,[],[f145,f35])).
% 0.18/0.42  fof(f35,plain,(
% 0.18/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.42    inference(cnf_transformation,[],[f6])).
% 0.18/0.42  fof(f6,axiom,(
% 0.18/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.18/0.42  fof(f145,plain,(
% 0.18/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0))))),
% 0.18/0.42    inference(subsumption_resolution,[],[f144,f28])).
% 0.18/0.42  fof(f144,plain,(
% 0.18/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0)))) | ~v1_relat_1(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f143,f32])).
% 0.18/0.42  fof(f32,plain,(
% 0.18/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f9])).
% 0.18/0.42  fof(f9,axiom,(
% 0.18/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.18/0.42  fof(f143,plain,(
% 0.18/0.42    r1_tarski(k2_relat_1(sK0),k2_relat_1(k6_relat_1(k2_relat_1(sK0)))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.18/0.42    inference(superposition,[],[f39,f47])).
% 0.18/0.42  fof(f47,plain,(
% 0.18/0.42    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.18/0.42    inference(resolution,[],[f28,f38])).
% 0.18/0.42  fof(f38,plain,(
% 0.18/0.42    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f17,plain,(
% 0.18/0.42    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f7])).
% 0.18/0.42  fof(f7,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.18/0.42  fof(f39,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f18])).
% 0.18/0.42  fof(f18,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.18/0.42  fof(f181,plain,(
% 0.18/0.42    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(superposition,[],[f52,f63])).
% 0.18/0.42  fof(f63,plain,(
% 0.18/0.42    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(forward_demodulation,[],[f62,f58])).
% 0.18/0.42  fof(f58,plain,(
% 0.18/0.42    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f57,f29])).
% 0.18/0.42  fof(f29,plain,(
% 0.18/0.42    v1_funct_1(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f57,plain,(
% 0.18/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f54,f30])).
% 0.18/0.42  fof(f30,plain,(
% 0.18/0.42    v2_funct_1(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f54,plain,(
% 0.18/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(resolution,[],[f28,f42])).
% 0.18/0.42  fof(f42,plain,(
% 0.18/0.42    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f23])).
% 0.18/0.42  fof(f23,plain,(
% 0.18/0.42    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(flattening,[],[f22])).
% 0.18/0.42  fof(f22,plain,(
% 0.18/0.42    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,axiom,(
% 0.18/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.18/0.42  fof(f62,plain,(
% 0.18/0.42    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.18/0.42    inference(subsumption_resolution,[],[f61,f29])).
% 0.18/0.42  fof(f61,plain,(
% 0.18/0.42    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f55,f30])).
% 0.18/0.42  fof(f55,plain,(
% 0.18/0.42    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(resolution,[],[f28,f43])).
% 0.18/0.42  fof(f43,plain,(
% 0.18/0.42    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f25])).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(flattening,[],[f24])).
% 0.18/0.42  fof(f24,plain,(
% 0.18/0.42    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f10])).
% 0.18/0.42  fof(f10,axiom,(
% 0.18/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.18/0.42  fof(f52,plain,(
% 0.18/0.42    ( ! [X4] : (~r1_tarski(k2_relat_1(sK0),k1_relat_1(X4)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X4)) | ~v1_relat_1(X4)) )),
% 0.18/0.42    inference(resolution,[],[f28,f41])).
% 0.18/0.42  fof(f41,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f21])).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(flattening,[],[f20])).
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.18/0.42  fof(f60,plain,(
% 0.18/0.42    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.18/0.42    inference(forward_demodulation,[],[f59,f58])).
% 0.18/0.42  fof(f59,plain,(
% 0.18/0.42    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.18/0.42    inference(backward_demodulation,[],[f31,f58])).
% 0.18/0.42  fof(f31,plain,(
% 0.18/0.42    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f201,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(superposition,[],[f98,f50])).
% 0.18/0.42  fof(f50,plain,(
% 0.18/0.42    ( ! [X2] : (k2_relat_1(k5_relat_1(sK0,X2)) = k9_relat_1(X2,k2_relat_1(sK0)) | ~v1_relat_1(X2)) )),
% 0.18/0.42    inference(resolution,[],[f28,f40])).
% 0.18/0.42  fof(f40,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f19])).
% 0.18/0.42  fof(f19,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.18/0.42  fof(f98,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.18/0.42    inference(forward_demodulation,[],[f97,f66])).
% 0.18/0.42  fof(f66,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.18/0.42    inference(forward_demodulation,[],[f65,f58])).
% 0.18/0.42  fof(f65,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.18/0.42    inference(subsumption_resolution,[],[f64,f29])).
% 0.18/0.42  fof(f64,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f56,f30])).
% 0.18/0.42  fof(f56,plain,(
% 0.18/0.42    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.18/0.42    inference(resolution,[],[f28,f44])).
% 0.18/0.42  fof(f44,plain,(
% 0.18/0.42    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f25])).
% 0.18/0.42  fof(f97,plain,(
% 0.18/0.42    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.18/0.42    inference(forward_demodulation,[],[f86,f63])).
% 0.18/0.42  fof(f86,plain,(
% 0.18/0.42    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.18/0.42    inference(resolution,[],[f45,f37])).
% 0.18/0.42  fof(f37,plain,(
% 0.18/0.42    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f16])).
% 0.18/0.42  fof(f16,plain,(
% 0.18/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.18/0.42  % SZS output end Proof for theBenchmark
% 0.18/0.42  % (3648)------------------------------
% 0.18/0.42  % (3648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (3648)Termination reason: Refutation
% 0.18/0.42  
% 0.18/0.42  % (3648)Memory used [KB]: 1791
% 0.18/0.42  % (3648)Time elapsed: 0.061 s
% 0.18/0.42  % (3648)------------------------------
% 0.18/0.42  % (3648)------------------------------
% 0.18/0.42  % (3636)Success in time 0.094 s
%------------------------------------------------------------------------------
