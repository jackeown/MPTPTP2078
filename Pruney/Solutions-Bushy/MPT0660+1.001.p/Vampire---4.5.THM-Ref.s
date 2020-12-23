%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0660+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   19
%              Number of atoms          :  163 ( 247 expanded)
%              Number of equality atoms :   57 (  75 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,(
    k6_relat_1(sK0) != k6_relat_1(sK0) ),
    inference(superposition,[],[f19,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(global_subsumption,[],[f20,f23,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f57,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f20,f23,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f20,f23,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0 ),
    inference(global_subsumption,[],[f20,f23,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(k6_relat_1(X0))) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_relat_1(k6_relat_1(X0)) = k1_relat_1(k2_funct_1(k6_relat_1(X0))) ) ),
    inference(resolution,[],[f28,f21])).

% (32348)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f21,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) ) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( X0 != X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) ) ),
    inference(forward_demodulation,[],[f48,f25])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) ) ),
    inference(forward_demodulation,[],[f47,f35])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) ) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k6_relat_1(X0) != k6_relat_1(X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k2_funct_1(k6_relat_1(X0)))
      | k2_relat_1(k6_relat_1(X0)) != k1_relat_1(k2_funct_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k2_funct_1(k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k2_funct_1(k6_relat_1(X0)))) ) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) ),
    inference(global_subsumption,[],[f20,f23,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f39,f24])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k5_relat_1(k6_relat_1(X0),k2_funct_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k6_relat_1(X0))) ) ),
    inference(resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f19,plain,(
    k6_relat_1(sK0) != k2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k6_relat_1(X0) != k2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

%------------------------------------------------------------------------------
