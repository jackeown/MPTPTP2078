%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 303 expanded)
%              Number of leaves         :   11 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  160 (1150 expanded)
%              Number of equality atoms :   53 ( 307 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f796])).

fof(f796,plain,(
    ! [X0] : k5_relat_1(k7_relat_1(sK0,X0),sK1) = k5_relat_1(k7_relat_1(sK0,X0),k7_relat_1(sK1,k9_relat_1(sK0,X0))) ),
    inference(subsumption_resolution,[],[f795,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
   => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).

fof(f795,plain,(
    ! [X0] :
      ( k5_relat_1(k7_relat_1(sK0,X0),sK1) = k5_relat_1(k7_relat_1(sK0,X0),k7_relat_1(sK1,k9_relat_1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f792,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f792,plain,(
    ! [X3] : k5_relat_1(k7_relat_1(sK0,X3),k7_relat_1(sK1,k2_relat_1(k7_relat_1(sK0,X3)))) = k5_relat_1(k7_relat_1(sK0,X3),sK1) ),
    inference(subsumption_resolution,[],[f790,f751])).

fof(f751,plain,(
    ! [X2] : v1_relat_1(k7_relat_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f750,f111])).

fof(f111,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k7_relat_1(sK0,X0),k6_relat_1(k2_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f107,f23])).

fof(f107,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k5_relat_1(k7_relat_1(sK0,X0),k6_relat_1(k2_relat_1(sK0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f105,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f105,plain,(
    ! [X8,X7] : k7_relat_1(k5_relat_1(sK0,k6_relat_1(X7)),X8) = k5_relat_1(k7_relat_1(sK0,X8),k6_relat_1(X7)) ),
    inference(resolution,[],[f47,f23])).

fof(f47,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | k7_relat_1(k5_relat_1(X4,k6_relat_1(X5)),X6) = k5_relat_1(k7_relat_1(X4,X6),k6_relat_1(X5)) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f750,plain,(
    ! [X2] : v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f749,f23])).

fof(f749,plain,(
    ! [X2] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0))))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f746,f24])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f746,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK0)
      | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0))))
      | ~ v1_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f745])).

fof(f745,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK0)
      | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0))))
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f110,f30])).

fof(f110,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(k5_relat_1(sK0,k6_relat_1(X4)))
      | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(X4)))
      | ~ v1_relat_1(k5_relat_1(sK0,k6_relat_1(X4))) ) ),
    inference(superposition,[],[f35,f105])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f790,plain,(
    ! [X3] :
      ( k5_relat_1(k7_relat_1(sK0,X3),k7_relat_1(sK1,k2_relat_1(k7_relat_1(sK0,X3)))) = k5_relat_1(k7_relat_1(sK0,X3),sK1)
      | ~ v1_relat_1(k7_relat_1(sK0,X3)) ) ),
    inference(superposition,[],[f772,f30])).

fof(f772,plain,(
    ! [X31,X32] : k5_relat_1(k5_relat_1(k7_relat_1(sK0,X31),k6_relat_1(X32)),sK1) = k5_relat_1(k7_relat_1(sK0,X31),k7_relat_1(sK1,X32)) ),
    inference(resolution,[],[f751,f515])).

fof(f515,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k7_relat_1(sK1,X4)) ) ),
    inference(backward_demodulation,[],[f236,f498])).

fof(f498,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(forward_demodulation,[],[f497,f116])).

fof(f116,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f112,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f112,plain,(
    ! [X0] :
      ( k7_relat_1(sK1,X0) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f106,f30])).

fof(f106,plain,(
    ! [X10,X9] : k7_relat_1(k5_relat_1(sK1,k6_relat_1(X9)),X10) = k5_relat_1(k7_relat_1(sK1,X10),k6_relat_1(X9)) ),
    inference(resolution,[],[f47,f25])).

fof(f497,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK1) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f494,f25])).

fof(f494,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(X0),sK1) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f488,f30])).

fof(f488,plain,(
    ! [X0,X1] : k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK1,k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f485,f25])).

fof(f485,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK1,k6_relat_1(X1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f398,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f398,plain,(
    ! [X4,X3] : k5_relat_1(k5_relat_1(k6_relat_1(X3),sK1),k6_relat_1(X4)) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK1,k6_relat_1(X4))) ),
    inference(resolution,[],[f388,f28])).

fof(f388,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | k5_relat_1(k5_relat_1(X9,sK1),k6_relat_1(X10)) = k5_relat_1(X9,k5_relat_1(sK1,k6_relat_1(X10))) ) ),
    inference(resolution,[],[f214,f25])).

fof(f214,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6)))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f31,f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f236,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK1)) ) ),
    inference(resolution,[],[f216,f28])).

fof(f216,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f31,f25])).

fof(f64,plain,(
    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k5_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f27,f62])).

fof(f62,plain,(
    ! [X5] : k7_relat_1(k5_relat_1(sK0,sK1),X5) = k5_relat_1(k7_relat_1(sK0,X5),sK1) ),
    inference(resolution,[],[f49,f23])).

fof(f49,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | k7_relat_1(k5_relat_1(X9,sK1),X10) = k5_relat_1(k7_relat_1(X9,X10),sK1) ) ),
    inference(resolution,[],[f34,f25])).

fof(f27,plain,(
    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (22156)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.47  % (22164)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.48  % (22148)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  % (22148)Refutation not found, incomplete strategy% (22148)------------------------------
% 0.21/0.48  % (22148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22148)Memory used [KB]: 10490
% 0.21/0.48  % (22148)Time elapsed: 0.075 s
% 0.21/0.48  % (22148)------------------------------
% 0.21/0.48  % (22148)------------------------------
% 0.21/0.49  % (22157)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (22147)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (22159)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (22167)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (22165)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (22162)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (22149)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (22146)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (22161)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (22151)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (22168)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (22155)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (22154)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (22152)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22163)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (22153)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (22160)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (22168)Refutation not found, incomplete strategy% (22168)------------------------------
% 0.21/0.52  % (22168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22168)Memory used [KB]: 10618
% 0.21/0.52  % (22168)Time elapsed: 0.116 s
% 0.21/0.52  % (22168)------------------------------
% 0.21/0.52  % (22168)------------------------------
% 0.21/0.52  % (22158)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (22150)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.41/0.54  % (22166)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.41/0.54  % (22145)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.41/0.55  % (22164)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f797,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(subsumption_resolution,[],[f64,f796])).
% 1.41/0.55  fof(f796,plain,(
% 1.41/0.55    ( ! [X0] : (k5_relat_1(k7_relat_1(sK0,X0),sK1) = k5_relat_1(k7_relat_1(sK0,X0),k7_relat_1(sK1,k9_relat_1(sK0,X0)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f795,f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    v1_relat_1(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    (k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,negated_conjecture,(
% 1.41/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 1.41/0.55    inference(negated_conjecture,[],[f8])).
% 1.41/0.55  fof(f8,conjecture,(
% 1.41/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).
% 1.41/0.55  fof(f795,plain,(
% 1.41/0.55    ( ! [X0] : (k5_relat_1(k7_relat_1(sK0,X0),sK1) = k5_relat_1(k7_relat_1(sK0,X0),k7_relat_1(sK1,k9_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 1.41/0.55    inference(superposition,[],[f792,f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.41/0.55  fof(f792,plain,(
% 1.41/0.55    ( ! [X3] : (k5_relat_1(k7_relat_1(sK0,X3),k7_relat_1(sK1,k2_relat_1(k7_relat_1(sK0,X3)))) = k5_relat_1(k7_relat_1(sK0,X3),sK1)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f790,f751])).
% 1.41/0.55  fof(f751,plain,(
% 1.41/0.55    ( ! [X2] : (v1_relat_1(k7_relat_1(sK0,X2))) )),
% 1.41/0.55    inference(forward_demodulation,[],[f750,f111])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k7_relat_1(sK0,X0),k6_relat_1(k2_relat_1(sK0)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f107,f23])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k7_relat_1(sK0,X0),k6_relat_1(k2_relat_1(sK0))) | ~v1_relat_1(sK0)) )),
% 1.41/0.55    inference(superposition,[],[f105,f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.41/0.55  fof(f105,plain,(
% 1.41/0.55    ( ! [X8,X7] : (k7_relat_1(k5_relat_1(sK0,k6_relat_1(X7)),X8) = k5_relat_1(k7_relat_1(sK0,X8),k6_relat_1(X7))) )),
% 1.41/0.55    inference(resolution,[],[f47,f23])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X4) | k7_relat_1(k5_relat_1(X4,k6_relat_1(X5)),X6) = k5_relat_1(k7_relat_1(X4,X6),k6_relat_1(X5))) )),
% 1.41/0.55    inference(resolution,[],[f34,f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 1.41/0.55  fof(f750,plain,(
% 1.41/0.55    ( ! [X2] : (v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0))))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f749,f23])).
% 1.41/0.55  fof(f749,plain,(
% 1.41/0.55    ( ! [X2] : (v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0)))) | ~v1_relat_1(sK0)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f746,f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    v1_funct_1(sK0)),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  fof(f746,plain,(
% 1.41/0.55    ( ! [X2] : (~v1_funct_1(sK0) | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0)))) | ~v1_relat_1(sK0)) )),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f745])).
% 1.41/0.55  fof(f745,plain,(
% 1.41/0.55    ( ! [X2] : (~v1_funct_1(sK0) | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X2),k6_relat_1(k2_relat_1(sK0)))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)) )),
% 1.41/0.55    inference(superposition,[],[f110,f30])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    ( ! [X4,X5] : (~v1_funct_1(k5_relat_1(sK0,k6_relat_1(X4))) | v1_relat_1(k5_relat_1(k7_relat_1(sK0,X5),k6_relat_1(X4))) | ~v1_relat_1(k5_relat_1(sK0,k6_relat_1(X4)))) )),
% 1.41/0.55    inference(superposition,[],[f35,f105])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f17])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.41/0.55  fof(f790,plain,(
% 1.41/0.55    ( ! [X3] : (k5_relat_1(k7_relat_1(sK0,X3),k7_relat_1(sK1,k2_relat_1(k7_relat_1(sK0,X3)))) = k5_relat_1(k7_relat_1(sK0,X3),sK1) | ~v1_relat_1(k7_relat_1(sK0,X3))) )),
% 1.41/0.55    inference(superposition,[],[f772,f30])).
% 1.41/0.55  fof(f772,plain,(
% 1.41/0.55    ( ! [X31,X32] : (k5_relat_1(k5_relat_1(k7_relat_1(sK0,X31),k6_relat_1(X32)),sK1) = k5_relat_1(k7_relat_1(sK0,X31),k7_relat_1(sK1,X32))) )),
% 1.41/0.55    inference(resolution,[],[f751,f515])).
% 1.41/0.55  fof(f515,plain,(
% 1.41/0.55    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k7_relat_1(sK1,X4))) )),
% 1.41/0.55    inference(backward_demodulation,[],[f236,f498])).
% 1.41/0.55  fof(f498,plain,(
% 1.41/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f497,f116])).
% 1.41/0.55  fof(f116,plain,(
% 1.41/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f112,f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    v1_relat_1(sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  fof(f112,plain,(
% 1.41/0.55    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK1)) )),
% 1.41/0.55    inference(superposition,[],[f106,f30])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    ( ! [X10,X9] : (k7_relat_1(k5_relat_1(sK1,k6_relat_1(X9)),X10) = k5_relat_1(k7_relat_1(sK1,X10),k6_relat_1(X9))) )),
% 1.41/0.55    inference(resolution,[],[f47,f25])).
% 1.41/0.55  fof(f497,plain,(
% 1.41/0.55    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK1) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f494,f25])).
% 1.41/0.55  fof(f494,plain,(
% 1.41/0.55    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK1) = k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(sK1)) )),
% 1.41/0.55    inference(superposition,[],[f488,f30])).
% 1.41/0.55  fof(f488,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK1,k6_relat_1(X1)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f485,f25])).
% 1.41/0.55  fof(f485,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k5_relat_1(k7_relat_1(sK1,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k5_relat_1(sK1,k6_relat_1(X1))) | ~v1_relat_1(sK1)) )),
% 1.41/0.55    inference(superposition,[],[f398,f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.41/0.55  fof(f398,plain,(
% 1.41/0.55    ( ! [X4,X3] : (k5_relat_1(k5_relat_1(k6_relat_1(X3),sK1),k6_relat_1(X4)) = k5_relat_1(k6_relat_1(X3),k5_relat_1(sK1,k6_relat_1(X4)))) )),
% 1.41/0.55    inference(resolution,[],[f388,f28])).
% 1.41/0.55  fof(f388,plain,(
% 1.41/0.55    ( ! [X10,X9] : (~v1_relat_1(X9) | k5_relat_1(k5_relat_1(X9,sK1),k6_relat_1(X10)) = k5_relat_1(X9,k5_relat_1(sK1,k6_relat_1(X10)))) )),
% 1.41/0.55    inference(resolution,[],[f214,f25])).
% 1.41/0.55  fof(f214,plain,(
% 1.41/0.55    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),k6_relat_1(X6)) = k5_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) | ~v1_relat_1(X4)) )),
% 1.41/0.55    inference(resolution,[],[f31,f28])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.41/0.55  fof(f236,plain,(
% 1.41/0.55    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK1))) )),
% 1.41/0.55    inference(resolution,[],[f216,f28])).
% 1.41/0.55  fof(f216,plain,(
% 1.41/0.55    ( ! [X10,X9] : (~v1_relat_1(X10) | k5_relat_1(k5_relat_1(X9,X10),sK1) = k5_relat_1(X9,k5_relat_1(X10,sK1)) | ~v1_relat_1(X9)) )),
% 1.41/0.55    inference(resolution,[],[f31,f25])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k5_relat_1(k7_relat_1(sK0,sK2),sK1)),
% 1.41/0.55    inference(backward_demodulation,[],[f27,f62])).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    ( ! [X5] : (k7_relat_1(k5_relat_1(sK0,sK1),X5) = k5_relat_1(k7_relat_1(sK0,X5),sK1)) )),
% 1.41/0.55    inference(resolution,[],[f49,f23])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X10,X9] : (~v1_relat_1(X9) | k7_relat_1(k5_relat_1(X9,sK1),X10) = k5_relat_1(k7_relat_1(X9,X10),sK1)) )),
% 1.41/0.55    inference(resolution,[],[f34,f25])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 1.41/0.55    inference(cnf_transformation,[],[f22])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (22164)------------------------------
% 1.41/0.55  % (22164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (22164)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (22164)Memory used [KB]: 7036
% 1.41/0.55  % (22164)Time elapsed: 0.133 s
% 1.41/0.55  % (22164)------------------------------
% 1.41/0.55  % (22164)------------------------------
% 1.41/0.55  % (22144)Success in time 0.194 s
%------------------------------------------------------------------------------
