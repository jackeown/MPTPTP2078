%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 232 expanded)
%              Number of leaves         :    9 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 ( 933 expanded)
%              Number of equality atoms :   67 ( 371 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,(
    k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(superposition,[],[f72,f107])).

fof(f107,plain,(
    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f106,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).

fof(f23,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f106,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f105,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f105,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f103,f25])).

fof(f103,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f102,f84])).

fof(f84,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0)) ),
    inference(superposition,[],[f45,f83])).

fof(f83,plain,(
    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f82,f41])).

fof(f41,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f32,f25])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f82,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f80,f43])).

fof(f43,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f47,f25])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(k4_relat_1(sK0),X0),k2_relat_1(sK0))
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(superposition,[],[f37,f41])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f101,f41])).

fof(f101,plain,(
    ! [X0] :
      ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f99,f43])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f78,f25])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k2_relat_1(k4_relat_1(X1)) = k2_relat_1(k5_relat_1(X2,k4_relat_1(X1)))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(X1)),k2_relat_1(X2)) ) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f72,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f53,f70])).

fof(f70,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f69,f46])).

fof(f46,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f31,f25])).

fof(f69,plain,(
    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f67,f41])).

fof(f67,plain,(
    k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0))) ),
    inference(resolution,[],[f59,f25])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f53,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f51,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f50,f25])).

fof(f50,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( ~ v1_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f52,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(backward_demodulation,[],[f28,f51])).

fof(f28,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (32180)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.47  % (32185)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.48  % (32185)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(sK0)),
% 0.20/0.48    inference(superposition,[],[f72,f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f106,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f105,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~v1_relat_1(k4_relat_1(sK0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f103,f25])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f102,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(superposition,[],[f45,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f82,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f32,f25])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f80,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f33,f25])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f47,f25])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k10_relat_1(k4_relat_1(X0),k2_relat_1(k4_relat_1(X0)))) )),
% 0.20/0.48    inference(resolution,[],[f31,f29])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k10_relat_1(k4_relat_1(sK0),X0),k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.20/0.48    inference(superposition,[],[f37,f41])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f101,f41])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f99,f43])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k4_relat_1(sK0)) = k2_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(X0))) )),
% 0.20/0.48    inference(resolution,[],[f78,f25])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k2_relat_1(k4_relat_1(X1)) = k2_relat_1(k5_relat_1(X2,k4_relat_1(X1))) | ~r1_tarski(k1_relat_1(k4_relat_1(X1)),k2_relat_1(X2))) )),
% 0.20/0.48    inference(resolution,[],[f35,f29])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f53,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f69,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f31,f25])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    k10_relat_1(sK0,k2_relat_1(sK0)) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f67,f41])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.48    inference(resolution,[],[f59,f25])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k10_relat_1(sK0,k1_relat_1(k4_relat_1(X0)))) )),
% 0.20/0.48    inference(resolution,[],[f54,f29])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK0,X0)) = k10_relat_1(sK0,k1_relat_1(X0))) )),
% 0.20/0.48    inference(resolution,[],[f34,f25])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f52,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.48    inference(resolution,[],[f50,f25])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.48    inference(resolution,[],[f48,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    v1_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ~v1_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.20/0.48    inference(resolution,[],[f36,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v2_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f28,f51])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (32185)------------------------------
% 0.20/0.48  % (32185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32185)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (32185)Memory used [KB]: 1663
% 0.20/0.48  % (32185)Time elapsed: 0.069 s
% 0.20/0.48  % (32185)------------------------------
% 0.20/0.48  % (32185)------------------------------
% 0.20/0.48  % (32170)Success in time 0.126 s
%------------------------------------------------------------------------------
