%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 355 expanded)
%              Number of leaves         :   12 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  188 (1506 expanded)
%              Number of equality atoms :   85 ( 583 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,(
    k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(superposition,[],[f143,f131])).

fof(f131,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(backward_demodulation,[],[f124,f130])).

fof(f130,plain,(
    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f129,f63])).

fof(f63,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f62,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,
    ( ~ v1_funct_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f60,f57])).

fof(f57,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f56,f27])).

fof(f56,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f55,f28])).

fof(f55,plain,
    ( ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f60,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f129,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(superposition,[],[f128,f71])).

fof(f71,plain,(
    k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f64,f70])).

fof(f70,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f69,f27])).

fof(f69,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f68,f28])).

fof(f68,plain,
    ( ~ v1_funct_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(forward_demodulation,[],[f67,f57])).

fof(f67,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    k4_relat_1(sK0) = k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(resolution,[],[f45,f27])).

fof(f45,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(X1) = k8_relat_1(k2_relat_1(k4_relat_1(X1)),k4_relat_1(X1)) ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f128,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK0),X0) = k1_relat_1(k8_relat_1(X0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f127,f111])).

fof(f111,plain,(
    ! [X0] : k8_relat_1(X0,k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0)) ),
    inference(resolution,[],[f54,f27])).

fof(f54,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | k8_relat_1(X3,k4_relat_1(X4)) = k5_relat_1(k4_relat_1(X4),k6_relat_1(X3)) ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f127,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),X0) ),
    inference(forward_demodulation,[],[f125,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f125,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f121,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f74,f27])).

fof(f74,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | k1_relat_1(k5_relat_1(k4_relat_1(X4),X3)) = k10_relat_1(k4_relat_1(X4),k1_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f124,plain,(
    k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f121,f27])).

fof(f143,plain,(
    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(backward_demodulation,[],[f59,f141])).

fof(f141,plain,(
    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f138,f47])).

fof(f47,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f138,plain,(
    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(resolution,[],[f137,f27])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f134,f70])).

fof(f134,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f88,f27])).

fof(f88,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | k2_relat_1(k5_relat_1(k4_relat_1(X4),X3)) = k9_relat_1(X3,k2_relat_1(k4_relat_1(X4)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f59,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f58,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(backward_demodulation,[],[f30,f57])).

fof(f30,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (18378)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.47  % (18385)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.48  % (18378)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (18377)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.48  % (18385)Refutation not found, incomplete strategy% (18385)------------------------------
% 0.21/0.48  % (18385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18385)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18385)Memory used [KB]: 1535
% 0.21/0.48  % (18385)Time elapsed: 0.046 s
% 0.21/0.48  % (18385)------------------------------
% 0.21/0.48  % (18385)------------------------------
% 0.21/0.48  % (18377)Refutation not found, incomplete strategy% (18377)------------------------------
% 0.21/0.48  % (18377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18377)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18377)Memory used [KB]: 10490
% 0.21/0.48  % (18377)Time elapsed: 0.046 s
% 0.21/0.48  % (18377)------------------------------
% 0.21/0.48  % (18377)------------------------------
% 0.21/0.48  % (18386)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k2_relat_1(sK0)),
% 0.21/0.49    inference(superposition,[],[f143,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f124,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f129,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f62,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f61,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f60,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f56,f27])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f55,f28])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f39,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f40,f29])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.49    inference(superposition,[],[f128,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    k4_relat_1(sK0) = k8_relat_1(k1_relat_1(sK0),k4_relat_1(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f64,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f69,f27])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f68,f28])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f67,f57])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f41,f29])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    k4_relat_1(sK0) = k8_relat_1(k2_relat_1(k4_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f45,f27])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(X1) = k8_relat_1(k2_relat_1(k4_relat_1(X1)),k4_relat_1(X1))) )),
% 0.21/0.49    inference(resolution,[],[f35,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(k4_relat_1(sK0),X0) = k1_relat_1(k8_relat_1(X0,k4_relat_1(sK0)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f127,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (k8_relat_1(X0,k4_relat_1(sK0)) = k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f54,f27])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v1_relat_1(X4) | k8_relat_1(X3,k4_relat_1(X4)) = k5_relat_1(k4_relat_1(X4),k6_relat_1(X3))) )),
% 0.21/0.49    inference(resolution,[],[f42,f34])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK0),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.49    inference(resolution,[],[f121,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f74,f27])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v1_relat_1(X4) | k1_relat_1(k5_relat_1(k4_relat_1(X4),X3)) = k10_relat_1(k4_relat_1(X4),k1_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(resolution,[],[f37,f34])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f121,f27])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k2_relat_1(sK0) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f59,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f138,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.49    inference(resolution,[],[f36,f27])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(resolution,[],[f137,f27])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k1_relat_1(sK0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f70])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) = k9_relat_1(X0,k2_relat_1(k4_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f88,f27])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v1_relat_1(X4) | k2_relat_1(k5_relat_1(k4_relat_1(X4),X3)) = k9_relat_1(X3,k2_relat_1(k4_relat_1(X4))) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(resolution,[],[f38,f34])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f58,f57])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f30,f57])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18378)------------------------------
% 0.21/0.49  % (18378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18378)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18378)Memory used [KB]: 1791
% 0.21/0.49  % (18378)Time elapsed: 0.063 s
% 0.21/0.49  % (18378)------------------------------
% 0.21/0.49  % (18378)------------------------------
% 0.21/0.49  % (18368)Success in time 0.131 s
%------------------------------------------------------------------------------
