%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 268 expanded)
%              Number of leaves         :    7 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  179 (1002 expanded)
%              Number of equality atoms :   58 ( 358 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

% (24123)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f130,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f129,f22])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f129,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f128,f28])).

% (24121)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f128,plain,(
    ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f127,f21])).

fof(f127,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f126,f80])).

fof(f80,plain,(
    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(superposition,[],[f20,f75])).

fof(f75,plain,(
    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(forward_demodulation,[],[f73,f32])).

fof(f32,plain,(
    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f73,plain,(
    k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    inference(resolution,[],[f71,f21])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k2_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f70,f36])).

fof(f36,plain,(
    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f35,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f34,f22])).

fof(f34,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k1_relat_1(k2_funct_1(sK0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f42,f22])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k1_relat_1(k5_relat_1(X1,k2_funct_1(X2))) = k10_relat_1(X1,k1_relat_1(k2_funct_1(X2)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f26,f28])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f20,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f126,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f67,f59])).

fof(f59,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f56,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f37,f54])).

fof(f54,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f49,plain,(
    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f48,f36])).

fof(f48,plain,(
    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f47,f40])).

fof(f40,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f39,f21])).

% (24135)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f39,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f38,f22])).

fof(f38,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f31,f23])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(k2_funct_1(X0)) = k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f24,f28])).

fof(f53,plain,(
    k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(subsumption_resolution,[],[f51,f21])).

fof(f51,plain,
    ( k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f44,f22])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(X0),sK0)) = k10_relat_1(k2_funct_1(X0),k1_relat_1(sK0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK0)) = k10_relat_1(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f26,f21])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)),k2_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(forward_demodulation,[],[f63,f40])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK0))
      | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) ) ),
    inference(superposition,[],[f27,f36])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (24120)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (24130)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (24129)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (24128)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (24116)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (24139)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (24130)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  % (24123)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~v1_relat_1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f128,f28])).
% 0.21/0.51  % (24121)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f21])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(superposition,[],[f20,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f24,f21])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f71,f21])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k2_relat_1(sK0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f70,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f21])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f34,f22])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f30,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f21])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) = k10_relat_1(X0,k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f22])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v1_funct_1(X2) | k1_relat_1(k5_relat_1(X1,k2_funct_1(X2))) = k10_relat_1(X1,k1_relat_1(k2_funct_1(X2))) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(resolution,[],[f26,f28])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f67,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f56,f21])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(superposition,[],[f37,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f53,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f48,f36])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f47,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f39,f21])).
% 0.21/0.51  % (24135)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f38,f22])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    inference(resolution,[],[f31,f23])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f45,f21])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK0)) = k10_relat_1(k2_funct_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f33,f22])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(k2_funct_1(X0)) = k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f24,f28])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f51,f21])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f44,f22])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(X0),sK0)) = k10_relat_1(k2_funct_1(X0),k1_relat_1(sK0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f41,f28])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK0)) = k10_relat_1(X0,k1_relat_1(sK0))) )),
% 0.21/0.51    inference(resolution,[],[f26,f21])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0)),k2_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.51    inference(superposition,[],[f25,f36])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0))) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f63,f40])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK0)) | k2_relat_1(k2_funct_1(sK0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK0)))) )),
% 0.21/0.51    inference(superposition,[],[f27,f36])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24130)------------------------------
% 0.21/0.51  % (24130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24130)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24130)Memory used [KB]: 6268
% 0.21/0.51  % (24130)Time elapsed: 0.084 s
% 0.21/0.51  % (24130)------------------------------
% 0.21/0.51  % (24130)------------------------------
% 0.21/0.51  % (24108)Success in time 0.151 s
%------------------------------------------------------------------------------
