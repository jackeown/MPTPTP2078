%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 150 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  240 ( 489 expanded)
%              Number of equality atoms :   58 ( 115 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f241,plain,(
    ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f239,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),X0) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f98,f129])).

fof(f129,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)) ),
    inference(subsumption_resolution,[],[f126,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f126,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f48,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f74,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

% (19428)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (19424)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (19412)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (19423)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f74,plain,(
    ! [X0] : k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f73,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f40,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f72,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f45,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f97,f93])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f86])).

fof(f86,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(subsumption_resolution,[],[f85,f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)) = X0
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)),X0) ) ),
    inference(resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)))
      | ~ r1_tarski(X3,X2) ) ),
    inference(forward_demodulation,[],[f94,f41])).

fof(f94,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)))
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) ) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)))
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f47,f86])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f239,plain,(
    sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f238,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f238,plain,
    ( sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f237,f32])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f237,plain,
    ( sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f211,f34])).

fof(f34,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f211,plain,
    ( sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f50,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f48,f45])).

fof(f35,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (19421)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (19416)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (19418)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (19413)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (19432)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (19410)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (19425)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (19433)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (19414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (19422)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (19415)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (19431)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (19417)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (19411)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (19414)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (19430)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (19429)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f241,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    sK0 != sK0 | ~r1_tarski(sK0,k1_relat_1(sK1))),
% 0.22/0.53    inference(superposition,[],[f239,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f98,f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f126,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.53    inference(superposition,[],[f48,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f74,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.53  % (19428)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (19424)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (19412)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (19423)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f73,f37])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f72,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f71,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(superposition,[],[f45,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f92,f37])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f90,f40])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(superposition,[],[f49,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f85,f37])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f84,f40])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f81,f38])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) | ~v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(superposition,[],[f50,f36])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)) = X0 | ~r1_tarski(k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 0.22/0.54    inference(resolution,[],[f95,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))) | ~r1_tarski(X3,X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f94,f41])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f37])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X3,k9_relat_1(k6_relat_1(X2),k9_relat_1(k6_relat_1(X2),X3))) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.54    inference(superposition,[],[f47,f86])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f238,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f237,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f211,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    v2_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    sK0 != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.54    inference(superposition,[],[f35,f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(X0,k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k10_relat_1(X0,k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f50,f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f127,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = k9_relat_1(k6_relat_1(k1_relat_1(X0)),X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f48,f45])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (19414)------------------------------
% 0.22/0.54  % (19414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19414)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (19414)Memory used [KB]: 6140
% 0.22/0.54  % (19414)Time elapsed: 0.109 s
% 0.22/0.54  % (19414)------------------------------
% 0.22/0.54  % (19414)------------------------------
% 0.22/0.54  % (19409)Success in time 0.175 s
%------------------------------------------------------------------------------
