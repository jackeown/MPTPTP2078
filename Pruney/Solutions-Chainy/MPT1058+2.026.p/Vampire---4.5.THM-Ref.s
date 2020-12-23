%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:20 EST 2020

% Result     : Theorem 12.61s
% Output     : Refutation 13.19s
% Verified   : 
% Statistics : Number of formulae       :  178 (110217 expanded)
%              Number of leaves         :   23 (29990 expanded)
%              Depth                    :   64
%              Number of atoms          :  302 (369278 expanded)
%              Number of equality atoms :  104 (24416 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29444,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28968,f135])).

fof(f135,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f134,f60])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f50,f49])).

% (8118)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
fof(f49,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f134,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f63,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f63,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f28968,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f28894,f111])).

fof(f111,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f62,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f28894,plain,(
    ! [X14,X15] : k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14) ),
    inference(subsumption_resolution,[],[f28814,f28333])).

fof(f28333,plain,(
    ! [X364,X365] : r1_tarski(k3_xboole_0(X364,X365),k3_xboole_0(X365,X364)) ),
    inference(superposition,[],[f22356,f21429])).

fof(f21429,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f20188,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f20188,plain,(
    ! [X12,X11] : k3_xboole_0(X11,X12) = k3_xboole_0(k3_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f19929,f14473])).

fof(f14473,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(forward_demodulation,[],[f14291,f604])).

fof(f604,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(superposition,[],[f585,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f585,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f550,f412])).

fof(f412,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f354,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f354,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),sK1) ),
    inference(resolution,[],[f352,f86])).

fof(f352,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,(
    ! [X0] :
      ( r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1)
      | r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1) ) ),
    inference(resolution,[],[f344,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f344,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK4(X9,sK1),k3_xboole_0(k1_xboole_0,X10))
      | r1_tarski(X9,sK1) ) ),
    inference(resolution,[],[f309,f76])).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(sK4(X0,sK1),X1)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f307,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f307,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK4(X2,sK1),k1_xboole_0)
      | r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f304,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f304,plain,(
    ! [X13] :
      ( r2_hidden(X13,sK1)
      | ~ r2_hidden(X13,k1_xboole_0) ) ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k10_relat_1(sK0,sK2))
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f114,f90])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k10_relat_1(sK0,sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f62,f90])).

fof(f550,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = X1 ),
    inference(resolution,[],[f500,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f500,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(k1_xboole_0,X3),X4) ),
    inference(resolution,[],[f493,f91])).

fof(f493,plain,(
    ! [X10,X9] : ~ r2_hidden(X9,k3_xboole_0(k1_xboole_0,X10)) ),
    inference(resolution,[],[f487,f76])).

fof(f487,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f472,f90])).

fof(f472,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f469,f437])).

fof(f437,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k1_xboole_0,sK1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f84,f412])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f469,plain,(
    r1_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f462,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f462,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k1_xboole_0,sK1) ) ),
    inference(resolution,[],[f448,f84])).

fof(f448,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_xboole_0,sK1),X1)
      | r1_xboole_0(k1_xboole_0,sK1) ) ),
    inference(subsumption_resolution,[],[f447,f64])).

fof(f447,plain,(
    ! [X1] :
      ( r1_xboole_0(k1_xboole_0,sK1)
      | r2_hidden(sK3(k1_xboole_0,sK1),X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f436,f90])).

fof(f436,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f83,f412])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f14291,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f81,f14217])).

fof(f14217,plain,(
    ! [X21,X20] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X20,X21),X20) ),
    inference(resolution,[],[f13440,f76])).

fof(f13440,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k1_xboole_0 = k4_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f13310,f85])).

fof(f13310,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(resolution,[],[f13265,f888])).

fof(f888,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k4_xboole_0(X3,X4),X4)
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f881,f86])).

fof(f881,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(resolution,[],[f797,f73])).

fof(f797,plain,(
    ! [X28,X27] :
      ( ~ r1_xboole_0(X27,X28)
      | k1_xboole_0 = k3_xboole_0(X27,X28) ) ),
    inference(resolution,[],[f755,f617])).

fof(f617,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f604,f85])).

fof(f755,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k3_xboole_0(X6,X7),X8)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f738,f84])).

fof(f738,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(X8,k1_xboole_0),X8)
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f490,f91])).

fof(f490,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(sK4(X3,k1_xboole_0),X3) ) ),
    inference(resolution,[],[f487,f91])).

fof(f13265,plain,(
    ! [X37,X38,X36] : r1_tarski(k4_xboole_0(X36,k2_xboole_0(X36,X37)),X38) ),
    inference(resolution,[],[f12514,f801])).

fof(f801,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f755,f72])).

fof(f72,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f12514,plain,(
    ! [X257,X259,X256,X258] : r1_xboole_0(k4_xboole_0(X256,X259),k4_xboole_0(X257,k2_xboole_0(X256,X258))) ),
    inference(forward_demodulation,[],[f12412,f615])).

fof(f615,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f606,f585])).

fof(f606,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f585,f81])).

fof(f12412,plain,(
    ! [X257,X259,X256,X258] : r1_xboole_0(k4_xboole_0(X256,X259),k4_xboole_0(k4_xboole_0(X257,k2_xboole_0(X256,X258)),k1_xboole_0)) ),
    inference(superposition,[],[f2746,f12275])).

fof(f12275,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(resolution,[],[f2610,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2610,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k3_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(resolution,[],[f2402,f797])).

fof(f2402,plain,(
    ! [X28,X29,X27] :
      ( r1_xboole_0(X29,k4_xboole_0(X28,X27))
      | ~ r1_tarski(X29,X27) ) ),
    inference(forward_demodulation,[],[f2346,f2378])).

fof(f2378,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f2330,f615])).

fof(f2330,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f1680,f569])).

fof(f569,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f568,f412])).

fof(f568,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f438,f566])).

fof(f566,plain,(
    ! [X8,X7] : k3_xboole_0(k1_xboole_0,X7) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f426,f551])).

fof(f551,plain,(
    ! [X2,X3] : k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3) ),
    inference(resolution,[],[f500,f86])).

fof(f426,plain,(
    ! [X8,X7] : k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k4_xboole_0(sK1,X8)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f421,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f421,plain,(
    ! [X8,X7] : k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k4_xboole_0(sK1,X8)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X7),X8) ),
    inference(superposition,[],[f94,f354])).

fof(f438,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f94,f412])).

fof(f1680,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k1_xboole_0) ),
    inference(superposition,[],[f80,f1638])).

fof(f1638,plain,(
    ! [X33,X34] : k1_xboole_0 = k3_xboole_0(X33,k4_xboole_0(X34,X33)) ),
    inference(resolution,[],[f1596,f617])).

fof(f1596,plain,(
    ! [X19,X17,X18] : r1_tarski(k3_xboole_0(X17,k4_xboole_0(X18,X17)),X19) ),
    inference(resolution,[],[f1406,f801])).

fof(f1406,plain,(
    ! [X2,X0,X3,X1] : r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f1397,f94])).

fof(f1397,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11)) ),
    inference(subsumption_resolution,[],[f1387,f472])).

fof(f1387,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11)),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11)) ) ),
    inference(superposition,[],[f83,f900])).

fof(f900,plain,(
    ! [X17,X15,X16] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f895,f620])).

fof(f620,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f604,f550])).

fof(f895,plain,(
    ! [X17,X15,X16] : k3_xboole_0(k1_xboole_0,X17) = k3_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X17)) ),
    inference(superposition,[],[f95,f881])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2346,plain,(
    ! [X28,X29,X27] :
      ( ~ r1_tarski(X29,k5_xboole_0(X27,k1_xboole_0))
      | r1_xboole_0(X29,k4_xboole_0(X28,X27)) ) ),
    inference(superposition,[],[f1136,f1680])).

fof(f1136,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X3,X4))
      | r1_xboole_0(X2,X4) ) ),
    inference(superposition,[],[f1124,f86])).

fof(f1124,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11) ),
    inference(subsumption_resolution,[],[f1113,f472])).

fof(f1113,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11),k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11) ) ),
    inference(superposition,[],[f83,f885])).

fof(f885,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(superposition,[],[f881,f94])).

fof(f2746,plain,(
    ! [X35,X33,X34] : r1_xboole_0(k4_xboole_0(X33,X35),k4_xboole_0(X34,k3_xboole_0(X33,X34))) ),
    inference(superposition,[],[f1154,f2381])).

fof(f2381,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,k3_xboole_0(X9,X10))) = X9 ),
    inference(backward_demodulation,[],[f1479,f2378])).

fof(f1479,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,k3_xboole_0(X9,X10))) = k5_xboole_0(X9,k1_xboole_0) ),
    inference(superposition,[],[f80,f1309])).

fof(f1309,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f1288,f94])).

fof(f1288,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(superposition,[],[f899,f72])).

fof(f899,plain,(
    ! [X14,X12,X13] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f894,f569])).

fof(f894,plain,(
    ! [X14,X12,X13] : k3_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X14)) = k4_xboole_0(k1_xboole_0,X14) ),
    inference(superposition,[],[f94,f881])).

fof(f1154,plain,(
    ! [X26,X24,X25] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X24,X25),X26),X25) ),
    inference(resolution,[],[f1136,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f19929,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2 ),
    inference(resolution,[],[f19859,f86])).

fof(f19859,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f74,f18594])).

fof(f18594,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f13915,f77])).

fof(f13915,plain,(
    ! [X33,X32] : k2_xboole_0(X33,X32) = k2_xboole_0(k2_xboole_0(X33,X32),X32) ),
    inference(forward_demodulation,[],[f13914,f585])).

fof(f13914,plain,(
    ! [X33,X32] : k2_xboole_0(k2_xboole_0(X33,X32),X32) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X33,X32)) ),
    inference(forward_demodulation,[],[f13751,f77])).

fof(f13751,plain,(
    ! [X33,X32] : k2_xboole_0(k2_xboole_0(X33,X32),X32) = k2_xboole_0(k2_xboole_0(X33,X32),k1_xboole_0) ),
    inference(superposition,[],[f81,f13441])).

fof(f13441,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f13310,f77])).

fof(f22356,plain,(
    ! [X165,X164] : r1_tarski(k3_xboole_0(X165,X164),X164) ),
    inference(superposition,[],[f19859,f22158])).

fof(f22158,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k3_xboole_0(X7,X8)) = X8 ),
    inference(forward_demodulation,[],[f21919,f604])).

fof(f21919,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f81,f21645])).

fof(f21645,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X6) ),
    inference(superposition,[],[f20190,f2062])).

fof(f2062,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f1173,f95])).

fof(f1173,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(k4_xboole_0(X4,X5),X6),X5) ),
    inference(resolution,[],[f1152,f797])).

fof(f1152,plain,(
    ! [X19,X20,X18] : r1_xboole_0(k3_xboole_0(k4_xboole_0(X18,X19),X20),X19) ),
    inference(resolution,[],[f1136,f76])).

fof(f20190,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k3_xboole_0(k4_xboole_0(X15,X16),X15) ),
    inference(superposition,[],[f19929,f3975])).

fof(f3975,plain,(
    ! [X39,X38] : k2_xboole_0(X38,k4_xboole_0(X38,X39)) = X38 ),
    inference(forward_demodulation,[],[f3904,f604])).

fof(f3904,plain,(
    ! [X39,X38] : k2_xboole_0(X38,k4_xboole_0(X38,X39)) = k2_xboole_0(X38,k1_xboole_0) ),
    inference(superposition,[],[f81,f3839])).

fof(f3839,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f3811,f3783])).

fof(f3783,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(k4_xboole_0(X8,X9),X8),X10) ),
    inference(resolution,[],[f3754,f797])).

fof(f3754,plain,(
    ! [X24,X23,X22] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X22,X23),X22),X24) ),
    inference(resolution,[],[f3034,f1265])).

fof(f1265,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f1153,f72])).

fof(f1153,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(k3_xboole_0(X21,X22),X23)
      | ~ r1_xboole_0(X21,X22) ) ),
    inference(resolution,[],[f1136,f755])).

fof(f3034,plain,(
    ! [X35,X33,X34,X32] : r1_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k4_xboole_0(X33,X34),X35)) ),
    inference(forward_demodulation,[],[f3010,f615])).

fof(f3010,plain,(
    ! [X35,X33,X34,X32] : r1_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,X34),k1_xboole_0),X35)) ),
    inference(superposition,[],[f2751,f899])).

fof(f2751,plain,(
    ! [X52,X50,X51] : r1_xboole_0(X50,k4_xboole_0(k4_xboole_0(X51,k3_xboole_0(X50,X51)),X52)) ),
    inference(superposition,[],[f1306,f2381])).

fof(f1306,plain,(
    ! [X17,X18,X16] : r1_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)) ),
    inference(subsumption_resolution,[],[f1296,f472])).

fof(f1296,plain,(
    ! [X17,X18,X16] :
      ( r2_hidden(sK3(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)) ) ),
    inference(superposition,[],[f83,f899])).

fof(f3811,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,X4),X3) = k3_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X3),X5) ),
    inference(resolution,[],[f3755,f86])).

fof(f3755,plain,(
    ! [X26,X27,X25] : r1_tarski(k4_xboole_0(k4_xboole_0(X25,X26),X25),X27) ),
    inference(resolution,[],[f3034,f801])).

fof(f28814,plain,(
    ! [X14,X15] :
      ( k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14)
      | ~ r1_tarski(k3_xboole_0(X15,X14),k3_xboole_0(X14,X15)) ) ),
    inference(resolution,[],[f28333,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (8081)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.49  % (8067)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (8072)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (8088)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (8073)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (8071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (8089)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (8089)Refutation not found, incomplete strategy% (8089)------------------------------
% 0.20/0.52  % (8089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8068)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (8089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8089)Memory used [KB]: 10746
% 0.20/0.53  % (8089)Time elapsed: 0.118 s
% 0.20/0.53  % (8089)------------------------------
% 0.20/0.53  % (8089)------------------------------
% 0.20/0.53  % (8069)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (8095)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (8091)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (8074)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (8070)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8090)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (8096)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (8093)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (8092)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (8094)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (8075)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (8084)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (8085)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8087)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (8084)Refutation not found, incomplete strategy% (8084)------------------------------
% 0.20/0.54  % (8084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8084)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8084)Memory used [KB]: 10618
% 0.20/0.54  % (8084)Time elapsed: 0.139 s
% 0.20/0.54  % (8084)------------------------------
% 0.20/0.54  % (8084)------------------------------
% 0.20/0.54  % (8076)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (8083)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (8080)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (8086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (8077)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (8079)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (8082)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (8077)Refutation not found, incomplete strategy% (8077)------------------------------
% 0.20/0.55  % (8077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8077)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8077)Memory used [KB]: 10746
% 0.20/0.55  % (8077)Time elapsed: 0.140 s
% 0.20/0.55  % (8077)------------------------------
% 0.20/0.55  % (8077)------------------------------
% 0.20/0.55  % (8078)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (8078)Refutation not found, incomplete strategy% (8078)------------------------------
% 0.20/0.55  % (8078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8078)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8078)Memory used [KB]: 10746
% 0.20/0.55  % (8078)Time elapsed: 0.150 s
% 0.20/0.55  % (8078)------------------------------
% 0.20/0.55  % (8078)------------------------------
% 2.17/0.64  % (8097)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.17/0.68  % (8098)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.17/0.70  % (8099)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.71  % (8100)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.15/0.81  % (8072)Time limit reached!
% 3.15/0.81  % (8072)------------------------------
% 3.15/0.81  % (8072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (8072)Termination reason: Time limit
% 3.15/0.83  % (8072)Termination phase: Saturation
% 3.15/0.83  
% 3.15/0.83  % (8072)Memory used [KB]: 10746
% 3.15/0.83  % (8072)Time elapsed: 0.400 s
% 3.15/0.83  % (8072)------------------------------
% 3.15/0.83  % (8072)------------------------------
% 4.01/0.90  % (8079)Time limit reached!
% 4.01/0.90  % (8079)------------------------------
% 4.01/0.90  % (8079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (8067)Time limit reached!
% 4.01/0.91  % (8067)------------------------------
% 4.01/0.91  % (8067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.92  % (8079)Termination reason: Time limit
% 4.29/0.92  
% 4.29/0.92  % (8079)Memory used [KB]: 10234
% 4.29/0.92  % (8079)Time elapsed: 0.503 s
% 4.29/0.92  % (8079)------------------------------
% 4.29/0.92  % (8079)------------------------------
% 4.29/0.93  % (8068)Time limit reached!
% 4.29/0.93  % (8068)------------------------------
% 4.29/0.93  % (8068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.29/0.93  % (8068)Termination reason: Time limit
% 4.29/0.93  
% 4.29/0.93  % (8068)Memory used [KB]: 9210
% 4.29/0.93  % (8068)Time elapsed: 0.517 s
% 4.29/0.93  % (8068)------------------------------
% 4.29/0.93  % (8068)------------------------------
% 4.29/0.93  % (8067)Termination reason: Time limit
% 4.29/0.93  % (8067)Termination phase: Saturation
% 4.29/0.93  
% 4.29/0.93  % (8067)Memory used [KB]: 4861
% 4.29/0.93  % (8067)Time elapsed: 0.500 s
% 4.29/0.93  % (8067)------------------------------
% 4.29/0.93  % (8067)------------------------------
% 4.43/0.96  % (8101)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.43/1.00  % (8083)Time limit reached!
% 4.43/1.00  % (8083)------------------------------
% 4.43/1.00  % (8083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.01  % (8083)Termination reason: Time limit
% 4.96/1.01  % (8083)Termination phase: Saturation
% 4.96/1.01  
% 4.96/1.01  % (8083)Memory used [KB]: 15991
% 4.96/1.01  % (8083)Time elapsed: 0.600 s
% 4.96/1.01  % (8083)------------------------------
% 4.96/1.01  % (8083)------------------------------
% 4.96/1.02  % (8095)Time limit reached!
% 4.96/1.02  % (8095)------------------------------
% 4.96/1.02  % (8095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.02  % (8095)Termination reason: Time limit
% 4.96/1.02  % (8095)Termination phase: Saturation
% 4.96/1.02  
% 4.96/1.02  % (8095)Memory used [KB]: 9466
% 4.96/1.02  % (8095)Time elapsed: 0.600 s
% 4.96/1.02  % (8095)------------------------------
% 4.96/1.02  % (8095)------------------------------
% 4.96/1.02  % (8100)Time limit reached!
% 4.96/1.02  % (8100)------------------------------
% 4.96/1.02  % (8100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.02  % (8100)Termination reason: Time limit
% 4.96/1.02  
% 4.96/1.02  % (8100)Memory used [KB]: 7419
% 4.96/1.02  % (8100)Time elapsed: 0.426 s
% 4.96/1.02  % (8100)------------------------------
% 4.96/1.02  % (8100)------------------------------
% 4.96/1.04  % (8074)Time limit reached!
% 4.96/1.04  % (8074)------------------------------
% 4.96/1.04  % (8074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.04  % (8103)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.96/1.05  % (8104)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.96/1.06  % (8074)Termination reason: Time limit
% 4.96/1.06  % (8074)Termination phase: Saturation
% 4.96/1.06  
% 4.96/1.06  % (8074)Memory used [KB]: 11385
% 4.96/1.06  % (8074)Time elapsed: 0.600 s
% 4.96/1.06  % (8074)------------------------------
% 4.96/1.06  % (8074)------------------------------
% 4.96/1.06  % (8102)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.67/1.13  % (8105)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.67/1.15  % (8107)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.67/1.15  % (8106)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.49/1.20  % (8108)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.49/1.21  % (8088)Time limit reached!
% 6.49/1.21  % (8088)------------------------------
% 6.49/1.21  % (8088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.49/1.22  % (8088)Termination reason: Time limit
% 6.49/1.22  % (8088)Termination phase: Saturation
% 6.49/1.22  
% 6.49/1.22  % (8088)Memory used [KB]: 8827
% 6.49/1.22  % (8088)Time elapsed: 0.800 s
% 6.49/1.22  % (8088)------------------------------
% 6.49/1.22  % (8088)------------------------------
% 6.85/1.28  % (8101)Time limit reached!
% 6.85/1.28  % (8101)------------------------------
% 6.85/1.28  % (8101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.28  % (8101)Termination reason: Time limit
% 6.85/1.28  % (8101)Termination phase: Saturation
% 6.85/1.28  
% 6.85/1.28  % (8101)Memory used [KB]: 14072
% 6.85/1.28  % (8101)Time elapsed: 0.400 s
% 6.85/1.28  % (8101)------------------------------
% 6.85/1.28  % (8101)------------------------------
% 7.41/1.34  % (8109)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.94/1.41  % (8069)Time limit reached!
% 7.94/1.41  % (8069)------------------------------
% 7.94/1.41  % (8069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.94/1.41  % (8110)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.94/1.43  % (8069)Termination reason: Time limit
% 7.94/1.43  
% 7.94/1.43  % (8069)Memory used [KB]: 21492
% 7.94/1.43  % (8069)Time elapsed: 1.007 s
% 7.94/1.43  % (8069)------------------------------
% 7.94/1.43  % (8069)------------------------------
% 9.09/1.54  % (8111)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.43/1.71  % (8093)Time limit reached!
% 10.43/1.71  % (8093)------------------------------
% 10.43/1.71  % (8093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.73  % (8091)Time limit reached!
% 10.43/1.73  % (8091)------------------------------
% 10.43/1.73  % (8091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.73  % (8091)Termination reason: Time limit
% 10.43/1.73  
% 10.43/1.73  % (8091)Memory used [KB]: 23666
% 10.43/1.73  % (8091)Time elapsed: 1.321 s
% 10.43/1.73  % (8091)------------------------------
% 10.43/1.73  % (8091)------------------------------
% 10.43/1.74  % (8093)Termination reason: Time limit
% 10.43/1.74  
% 10.43/1.74  % (8093)Memory used [KB]: 23027
% 10.43/1.74  % (8093)Time elapsed: 1.306 s
% 10.43/1.74  % (8093)------------------------------
% 10.43/1.74  % (8093)------------------------------
% 10.43/1.75  % (8082)Time limit reached!
% 10.43/1.75  % (8082)------------------------------
% 10.43/1.75  % (8082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.43/1.75  % (8082)Termination reason: Time limit
% 10.43/1.75  
% 10.43/1.75  % (8082)Memory used [KB]: 12792
% 10.43/1.75  % (8082)Time elapsed: 1.302 s
% 10.43/1.75  % (8082)------------------------------
% 10.43/1.75  % (8082)------------------------------
% 11.26/1.79  % (8109)Time limit reached!
% 11.26/1.79  % (8109)------------------------------
% 11.26/1.79  % (8109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.26/1.79  % (8109)Termination reason: Time limit
% 11.26/1.79  
% 11.26/1.79  % (8109)Memory used [KB]: 5117
% 11.26/1.79  % (8109)Time elapsed: 0.522 s
% 11.26/1.79  % (8109)------------------------------
% 11.26/1.79  % (8109)------------------------------
% 11.52/1.85  % (8114)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.52/1.89  % (8115)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.52/1.89  % (8113)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.52/1.90  % (8116)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.10/1.92  % (8094)Time limit reached!
% 12.10/1.92  % (8094)------------------------------
% 12.10/1.92  % (8094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.10/1.92  % (8094)Termination reason: Time limit
% 12.10/1.92  % (8094)Termination phase: Saturation
% 12.10/1.92  
% 12.10/1.92  % (8094)Memory used [KB]: 15223
% 12.10/1.92  % (8094)Time elapsed: 1.500 s
% 12.10/1.92  % (8094)------------------------------
% 12.10/1.92  % (8094)------------------------------
% 12.10/1.92  % (8071)Time limit reached!
% 12.10/1.92  % (8071)------------------------------
% 12.10/1.92  % (8071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.10/1.92  % (8071)Termination reason: Time limit
% 12.10/1.92  % (8071)Termination phase: Saturation
% 12.10/1.92  
% 12.10/1.92  % (8071)Memory used [KB]: 18549
% 12.10/1.92  % (8071)Time elapsed: 1.500 s
% 12.10/1.92  % (8071)------------------------------
% 12.10/1.92  % (8071)------------------------------
% 12.61/2.05  % (8117)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.61/2.06  % (8090)Refutation found. Thanks to Tanya!
% 12.61/2.06  % SZS status Theorem for theBenchmark
% 12.61/2.06  % SZS output start Proof for theBenchmark
% 12.61/2.06  fof(f29444,plain,(
% 12.61/2.06    $false),
% 12.61/2.06    inference(subsumption_resolution,[],[f28968,f135])).
% 12.61/2.06  fof(f135,plain,(
% 12.61/2.06    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 12.61/2.06    inference(subsumption_resolution,[],[f134,f60])).
% 12.61/2.06  fof(f60,plain,(
% 12.61/2.06    v1_relat_1(sK0)),
% 12.61/2.06    inference(cnf_transformation,[],[f51])).
% 12.61/2.06  fof(f51,plain,(
% 12.61/2.06    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 12.61/2.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f50,f49])).
% 12.61/2.07  % (8118)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.19/2.09  fof(f49,plain,(
% 13.19/2.09    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 13.19/2.09    introduced(choice_axiom,[])).
% 13.19/2.09  fof(f50,plain,(
% 13.19/2.09    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 13.19/2.09    introduced(choice_axiom,[])).
% 13.19/2.09  fof(f38,plain,(
% 13.19/2.09    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 13.19/2.09    inference(flattening,[],[f37])).
% 13.19/2.09  fof(f37,plain,(
% 13.19/2.09    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 13.19/2.09    inference(ennf_transformation,[],[f34])).
% 13.19/2.09  fof(f34,negated_conjecture,(
% 13.19/2.09    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 13.19/2.09    inference(negated_conjecture,[],[f33])).
% 13.19/2.09  fof(f33,conjecture,(
% 13.19/2.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 13.19/2.09  fof(f134,plain,(
% 13.19/2.09    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 13.19/2.09    inference(superposition,[],[f63,f96])).
% 13.19/2.09  fof(f96,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f45])).
% 13.19/2.09  fof(f45,plain,(
% 13.19/2.09    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 13.19/2.09    inference(ennf_transformation,[],[f31])).
% 13.19/2.09  fof(f31,axiom,(
% 13.19/2.09    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 13.19/2.09  fof(f63,plain,(
% 13.19/2.09    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 13.19/2.09    inference(cnf_transformation,[],[f51])).
% 13.19/2.09  fof(f28968,plain,(
% 13.19/2.09    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 13.19/2.09    inference(superposition,[],[f28894,f111])).
% 13.19/2.09  fof(f111,plain,(
% 13.19/2.09    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 13.19/2.09    inference(resolution,[],[f62,f86])).
% 13.19/2.09  fof(f86,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f43])).
% 13.19/2.09  fof(f43,plain,(
% 13.19/2.09    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 13.19/2.09    inference(ennf_transformation,[],[f10])).
% 13.19/2.09  fof(f10,axiom,(
% 13.19/2.09    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 13.19/2.09  fof(f62,plain,(
% 13.19/2.09    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 13.19/2.09    inference(cnf_transformation,[],[f51])).
% 13.19/2.09  fof(f28894,plain,(
% 13.19/2.09    ( ! [X14,X15] : (k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14)) )),
% 13.19/2.09    inference(subsumption_resolution,[],[f28814,f28333])).
% 13.19/2.09  fof(f28333,plain,(
% 13.19/2.09    ( ! [X364,X365] : (r1_tarski(k3_xboole_0(X364,X365),k3_xboole_0(X365,X364))) )),
% 13.19/2.09    inference(superposition,[],[f22356,f21429])).
% 13.19/2.09  fof(f21429,plain,(
% 13.19/2.09    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 13.19/2.09    inference(superposition,[],[f20188,f95])).
% 13.19/2.09  fof(f95,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 13.19/2.09    inference(cnf_transformation,[],[f8])).
% 13.19/2.09  fof(f8,axiom,(
% 13.19/2.09    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 13.19/2.09  fof(f20188,plain,(
% 13.19/2.09    ( ! [X12,X11] : (k3_xboole_0(X11,X12) = k3_xboole_0(k3_xboole_0(X11,X12),X11)) )),
% 13.19/2.09    inference(superposition,[],[f19929,f14473])).
% 13.19/2.09  fof(f14473,plain,(
% 13.19/2.09    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) )),
% 13.19/2.09    inference(forward_demodulation,[],[f14291,f604])).
% 13.19/2.09  fof(f604,plain,(
% 13.19/2.09    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 13.19/2.09    inference(superposition,[],[f585,f77])).
% 13.19/2.09  fof(f77,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f1])).
% 13.19/2.09  fof(f1,axiom,(
% 13.19/2.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 13.19/2.09  fof(f585,plain,(
% 13.19/2.09    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 13.19/2.09    inference(superposition,[],[f550,f412])).
% 13.19/2.09  fof(f412,plain,(
% 13.19/2.09    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 13.19/2.09    inference(superposition,[],[f354,f65])).
% 13.19/2.09  fof(f65,plain,(
% 13.19/2.09    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f11])).
% 13.19/2.09  fof(f11,axiom,(
% 13.19/2.09    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 13.19/2.09  fof(f354,plain,(
% 13.19/2.09    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),sK1)) )),
% 13.19/2.09    inference(resolution,[],[f352,f86])).
% 13.19/2.09  fof(f352,plain,(
% 13.19/2.09    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1)) )),
% 13.19/2.09    inference(duplicate_literal_removal,[],[f347])).
% 13.19/2.09  fof(f347,plain,(
% 13.19/2.09    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1) | r1_tarski(k3_xboole_0(k1_xboole_0,X0),sK1)) )),
% 13.19/2.09    inference(resolution,[],[f344,f91])).
% 13.19/2.09  fof(f91,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f59])).
% 13.19/2.09  fof(f59,plain,(
% 13.19/2.09    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 13.19/2.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 13.19/2.09  fof(f58,plain,(
% 13.19/2.09    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 13.19/2.09    introduced(choice_axiom,[])).
% 13.19/2.09  fof(f57,plain,(
% 13.19/2.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 13.19/2.09    inference(rectify,[],[f56])).
% 13.19/2.09  fof(f56,plain,(
% 13.19/2.09    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 13.19/2.09    inference(nnf_transformation,[],[f44])).
% 13.19/2.09  fof(f44,plain,(
% 13.19/2.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 13.19/2.09    inference(ennf_transformation,[],[f2])).
% 13.19/2.09  fof(f2,axiom,(
% 13.19/2.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 13.19/2.09  fof(f344,plain,(
% 13.19/2.09    ( ! [X10,X9] : (~r2_hidden(sK4(X9,sK1),k3_xboole_0(k1_xboole_0,X10)) | r1_tarski(X9,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f309,f76])).
% 13.19/2.09  fof(f76,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f9])).
% 13.19/2.09  fof(f9,axiom,(
% 13.19/2.09    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 13.19/2.09  fof(f309,plain,(
% 13.19/2.09    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(sK4(X0,sK1),X1) | r1_tarski(X0,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f307,f90])).
% 13.19/2.09  fof(f90,plain,(
% 13.19/2.09    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f59])).
% 13.19/2.09  fof(f307,plain,(
% 13.19/2.09    ( ! [X2] : (~r2_hidden(sK4(X2,sK1),k1_xboole_0) | r1_tarski(X2,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f304,f92])).
% 13.19/2.09  fof(f92,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f59])).
% 13.19/2.09  fof(f304,plain,(
% 13.19/2.09    ( ! [X13] : (r2_hidden(X13,sK1) | ~r2_hidden(X13,k1_xboole_0)) )),
% 13.19/2.09    inference(resolution,[],[f133,f64])).
% 13.19/2.09  fof(f64,plain,(
% 13.19/2.09    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f12])).
% 13.19/2.09  fof(f12,axiom,(
% 13.19/2.09    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 13.19/2.09  fof(f133,plain,(
% 13.19/2.09    ( ! [X2,X1] : (~r1_tarski(X2,k10_relat_1(sK0,sK2)) | ~r2_hidden(X1,X2) | r2_hidden(X1,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f114,f90])).
% 13.19/2.09  fof(f114,plain,(
% 13.19/2.09    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK0,sK2)) | r2_hidden(X0,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f62,f90])).
% 13.19/2.09  fof(f550,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) = X1) )),
% 13.19/2.09    inference(resolution,[],[f500,f85])).
% 13.19/2.09  fof(f85,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f42])).
% 13.19/2.09  fof(f42,plain,(
% 13.19/2.09    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 13.19/2.09    inference(ennf_transformation,[],[f7])).
% 13.19/2.09  fof(f7,axiom,(
% 13.19/2.09    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 13.19/2.09  fof(f500,plain,(
% 13.19/2.09    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(k1_xboole_0,X3),X4)) )),
% 13.19/2.09    inference(resolution,[],[f493,f91])).
% 13.19/2.09  fof(f493,plain,(
% 13.19/2.09    ( ! [X10,X9] : (~r2_hidden(X9,k3_xboole_0(k1_xboole_0,X10))) )),
% 13.19/2.09    inference(resolution,[],[f487,f76])).
% 13.19/2.09  fof(f487,plain,(
% 13.19/2.09    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 13.19/2.09    inference(resolution,[],[f472,f90])).
% 13.19/2.09  fof(f472,plain,(
% 13.19/2.09    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 13.19/2.09    inference(resolution,[],[f469,f437])).
% 13.19/2.09  fof(f437,plain,(
% 13.19/2.09    ( ! [X2] : (~r1_xboole_0(k1_xboole_0,sK1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f84,f412])).
% 13.19/2.09  fof(f84,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 13.19/2.09    inference(cnf_transformation,[],[f53])).
% 13.19/2.09  fof(f53,plain,(
% 13.19/2.09    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 13.19/2.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f52])).
% 13.19/2.09  fof(f52,plain,(
% 13.19/2.09    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 13.19/2.09    introduced(choice_axiom,[])).
% 13.19/2.09  fof(f41,plain,(
% 13.19/2.09    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 13.19/2.09    inference(ennf_transformation,[],[f36])).
% 13.19/2.09  fof(f36,plain,(
% 13.19/2.09    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 13.19/2.09    inference(rectify,[],[f4])).
% 13.19/2.09  fof(f4,axiom,(
% 13.19/2.09    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 13.19/2.09  fof(f469,plain,(
% 13.19/2.09    r1_xboole_0(k1_xboole_0,sK1)),
% 13.19/2.09    inference(resolution,[],[f462,f73])).
% 13.19/2.09  fof(f73,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f16])).
% 13.19/2.09  fof(f16,axiom,(
% 13.19/2.09    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 13.19/2.09  fof(f462,plain,(
% 13.19/2.09    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k1_xboole_0,sK1)) )),
% 13.19/2.09    inference(resolution,[],[f448,f84])).
% 13.19/2.09  fof(f448,plain,(
% 13.19/2.09    ( ! [X1] : (r2_hidden(sK3(k1_xboole_0,sK1),X1) | r1_xboole_0(k1_xboole_0,sK1)) )),
% 13.19/2.09    inference(subsumption_resolution,[],[f447,f64])).
% 13.19/2.09  fof(f447,plain,(
% 13.19/2.09    ( ! [X1] : (r1_xboole_0(k1_xboole_0,sK1) | r2_hidden(sK3(k1_xboole_0,sK1),X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 13.19/2.09    inference(resolution,[],[f436,f90])).
% 13.19/2.09  fof(f436,plain,(
% 13.19/2.09    r2_hidden(sK3(k1_xboole_0,sK1),k1_xboole_0) | r1_xboole_0(k1_xboole_0,sK1)),
% 13.19/2.09    inference(superposition,[],[f83,f412])).
% 13.19/2.09  fof(f83,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f53])).
% 13.19/2.09  fof(f14291,plain,(
% 13.19/2.09    ( ! [X6,X7] : (k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 13.19/2.09    inference(superposition,[],[f81,f14217])).
% 13.19/2.09  fof(f14217,plain,(
% 13.19/2.09    ( ! [X21,X20] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X20,X21),X20)) )),
% 13.19/2.09    inference(resolution,[],[f13440,f76])).
% 13.19/2.09  fof(f13440,plain,(
% 13.19/2.09    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k1_xboole_0 = k4_xboole_0(X1,X2)) )),
% 13.19/2.09    inference(superposition,[],[f13310,f85])).
% 13.19/2.09  fof(f13310,plain,(
% 13.19/2.09    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 13.19/2.09    inference(resolution,[],[f13265,f888])).
% 13.19/2.09  fof(f888,plain,(
% 13.19/2.09    ( ! [X4,X3] : (~r1_tarski(k4_xboole_0(X3,X4),X4) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 13.19/2.09    inference(superposition,[],[f881,f86])).
% 13.19/2.09  fof(f881,plain,(
% 13.19/2.09    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X2),X2)) )),
% 13.19/2.09    inference(resolution,[],[f797,f73])).
% 13.19/2.09  fof(f797,plain,(
% 13.19/2.09    ( ! [X28,X27] : (~r1_xboole_0(X27,X28) | k1_xboole_0 = k3_xboole_0(X27,X28)) )),
% 13.19/2.09    inference(resolution,[],[f755,f617])).
% 13.19/2.09  fof(f617,plain,(
% 13.19/2.09    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 13.19/2.09    inference(superposition,[],[f604,f85])).
% 13.19/2.09  fof(f755,plain,(
% 13.19/2.09    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,X7),X8) | ~r1_xboole_0(X6,X7)) )),
% 13.19/2.09    inference(resolution,[],[f738,f84])).
% 13.19/2.09  fof(f738,plain,(
% 13.19/2.09    ( ! [X8,X9] : (r2_hidden(sK4(X8,k1_xboole_0),X8) | r1_tarski(X8,X9)) )),
% 13.19/2.09    inference(resolution,[],[f490,f91])).
% 13.19/2.09  fof(f490,plain,(
% 13.19/2.09    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(sK4(X3,k1_xboole_0),X3)) )),
% 13.19/2.09    inference(resolution,[],[f487,f91])).
% 13.19/2.09  fof(f13265,plain,(
% 13.19/2.09    ( ! [X37,X38,X36] : (r1_tarski(k4_xboole_0(X36,k2_xboole_0(X36,X37)),X38)) )),
% 13.19/2.09    inference(resolution,[],[f12514,f801])).
% 13.19/2.09  fof(f801,plain,(
% 13.19/2.09    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_tarski(X2,X3)) )),
% 13.19/2.09    inference(superposition,[],[f755,f72])).
% 13.19/2.09  fof(f72,plain,(
% 13.19/2.09    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 13.19/2.09    inference(cnf_transformation,[],[f35])).
% 13.19/2.09  fof(f35,plain,(
% 13.19/2.09    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 13.19/2.09    inference(rectify,[],[f3])).
% 13.19/2.09  fof(f3,axiom,(
% 13.19/2.09    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 13.19/2.09  fof(f12514,plain,(
% 13.19/2.09    ( ! [X257,X259,X256,X258] : (r1_xboole_0(k4_xboole_0(X256,X259),k4_xboole_0(X257,k2_xboole_0(X256,X258)))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f12412,f615])).
% 13.19/2.09  fof(f615,plain,(
% 13.19/2.09    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 13.19/2.09    inference(forward_demodulation,[],[f606,f585])).
% 13.19/2.09  fof(f606,plain,(
% 13.19/2.09    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X4,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f585,f81])).
% 13.19/2.09  fof(f12412,plain,(
% 13.19/2.09    ( ! [X257,X259,X256,X258] : (r1_xboole_0(k4_xboole_0(X256,X259),k4_xboole_0(k4_xboole_0(X257,k2_xboole_0(X256,X258)),k1_xboole_0))) )),
% 13.19/2.09    inference(superposition,[],[f2746,f12275])).
% 13.19/2.09  fof(f12275,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 13.19/2.09    inference(resolution,[],[f2610,f74])).
% 13.19/2.09  fof(f74,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 13.19/2.09    inference(cnf_transformation,[],[f17])).
% 13.19/2.09  fof(f17,axiom,(
% 13.19/2.09    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 13.19/2.09  fof(f2610,plain,(
% 13.19/2.09    ( ! [X10,X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k3_xboole_0(X8,k4_xboole_0(X10,X9))) )),
% 13.19/2.09    inference(resolution,[],[f2402,f797])).
% 13.19/2.09  fof(f2402,plain,(
% 13.19/2.09    ( ! [X28,X29,X27] : (r1_xboole_0(X29,k4_xboole_0(X28,X27)) | ~r1_tarski(X29,X27)) )),
% 13.19/2.09    inference(forward_demodulation,[],[f2346,f2378])).
% 13.19/2.09  fof(f2378,plain,(
% 13.19/2.09    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 13.19/2.09    inference(forward_demodulation,[],[f2330,f615])).
% 13.19/2.09  fof(f2330,plain,(
% 13.19/2.09    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f1680,f569])).
% 13.19/2.09  fof(f569,plain,(
% 13.19/2.09    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 13.19/2.09    inference(forward_demodulation,[],[f568,f412])).
% 13.19/2.09  fof(f568,plain,(
% 13.19/2.09    ( ! [X3] : (k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,X3)) )),
% 13.19/2.09    inference(backward_demodulation,[],[f438,f566])).
% 13.19/2.09  fof(f566,plain,(
% 13.19/2.09    ( ! [X8,X7] : (k3_xboole_0(k1_xboole_0,X7) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8))) )),
% 13.19/2.09    inference(backward_demodulation,[],[f426,f551])).
% 13.19/2.09  fof(f551,plain,(
% 13.19/2.09    ( ! [X2,X3] : (k3_xboole_0(k1_xboole_0,X2) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3)) )),
% 13.19/2.09    inference(resolution,[],[f500,f86])).
% 13.19/2.09  fof(f426,plain,(
% 13.19/2.09    ( ! [X8,X7] : (k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k4_xboole_0(sK1,X8)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f421,f94])).
% 13.19/2.09  fof(f94,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f15])).
% 13.19/2.09  fof(f15,axiom,(
% 13.19/2.09    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 13.19/2.09  fof(f421,plain,(
% 13.19/2.09    ( ! [X8,X7] : (k3_xboole_0(k3_xboole_0(k1_xboole_0,X7),k4_xboole_0(sK1,X8)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X7),X8)) )),
% 13.19/2.09    inference(superposition,[],[f94,f354])).
% 13.19/2.09  fof(f438,plain,(
% 13.19/2.09    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 13.19/2.09    inference(superposition,[],[f94,f412])).
% 13.19/2.09  fof(f1680,plain,(
% 13.19/2.09    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f80,f1638])).
% 13.19/2.09  fof(f1638,plain,(
% 13.19/2.09    ( ! [X33,X34] : (k1_xboole_0 = k3_xboole_0(X33,k4_xboole_0(X34,X33))) )),
% 13.19/2.09    inference(resolution,[],[f1596,f617])).
% 13.19/2.09  fof(f1596,plain,(
% 13.19/2.09    ( ! [X19,X17,X18] : (r1_tarski(k3_xboole_0(X17,k4_xboole_0(X18,X17)),X19)) )),
% 13.19/2.09    inference(resolution,[],[f1406,f801])).
% 13.19/2.09  fof(f1406,plain,(
% 13.19/2.09    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X2,X3))) )),
% 13.19/2.09    inference(superposition,[],[f1397,f94])).
% 13.19/2.09  fof(f1397,plain,(
% 13.19/2.09    ( ! [X10,X11,X9] : (r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11))) )),
% 13.19/2.09    inference(subsumption_resolution,[],[f1387,f472])).
% 13.19/2.09  fof(f1387,plain,(
% 13.19/2.09    ( ! [X10,X11,X9] : (r2_hidden(sK3(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11)),k1_xboole_0) | r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X10,X11))) )),
% 13.19/2.09    inference(superposition,[],[f83,f900])).
% 13.19/2.09  fof(f900,plain,(
% 13.19/2.09    ( ! [X17,X15,X16] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X17))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f895,f620])).
% 13.19/2.09  fof(f620,plain,(
% 13.19/2.09    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 13.19/2.09    inference(superposition,[],[f604,f550])).
% 13.19/2.09  fof(f895,plain,(
% 13.19/2.09    ( ! [X17,X15,X16] : (k3_xboole_0(k1_xboole_0,X17) = k3_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X17))) )),
% 13.19/2.09    inference(superposition,[],[f95,f881])).
% 13.19/2.09  fof(f80,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 13.19/2.09    inference(cnf_transformation,[],[f6])).
% 13.19/2.09  fof(f6,axiom,(
% 13.19/2.09    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 13.19/2.09  fof(f2346,plain,(
% 13.19/2.09    ( ! [X28,X29,X27] : (~r1_tarski(X29,k5_xboole_0(X27,k1_xboole_0)) | r1_xboole_0(X29,k4_xboole_0(X28,X27))) )),
% 13.19/2.09    inference(superposition,[],[f1136,f1680])).
% 13.19/2.09  fof(f1136,plain,(
% 13.19/2.09    ( ! [X4,X2,X3] : (~r1_tarski(X2,k4_xboole_0(X3,X4)) | r1_xboole_0(X2,X4)) )),
% 13.19/2.09    inference(superposition,[],[f1124,f86])).
% 13.19/2.09  fof(f1124,plain,(
% 13.19/2.09    ( ! [X10,X11,X9] : (r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)) )),
% 13.19/2.09    inference(subsumption_resolution,[],[f1113,f472])).
% 13.19/2.09  fof(f1113,plain,(
% 13.19/2.09    ( ! [X10,X11,X9] : (r2_hidden(sK3(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11),k1_xboole_0) | r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)) )),
% 13.19/2.09    inference(superposition,[],[f83,f885])).
% 13.19/2.09  fof(f885,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2)) )),
% 13.19/2.09    inference(superposition,[],[f881,f94])).
% 13.19/2.09  fof(f2746,plain,(
% 13.19/2.09    ( ! [X35,X33,X34] : (r1_xboole_0(k4_xboole_0(X33,X35),k4_xboole_0(X34,k3_xboole_0(X33,X34)))) )),
% 13.19/2.09    inference(superposition,[],[f1154,f2381])).
% 13.19/2.09  fof(f2381,plain,(
% 13.19/2.09    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,k3_xboole_0(X9,X10))) = X9) )),
% 13.19/2.09    inference(backward_demodulation,[],[f1479,f2378])).
% 13.19/2.09  fof(f1479,plain,(
% 13.19/2.09    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,k3_xboole_0(X9,X10))) = k5_xboole_0(X9,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f80,f1309])).
% 13.19/2.09  fof(f1309,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 13.19/2.09    inference(superposition,[],[f1288,f94])).
% 13.19/2.09  fof(f1288,plain,(
% 13.19/2.09    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 13.19/2.09    inference(superposition,[],[f899,f72])).
% 13.19/2.09  fof(f899,plain,(
% 13.19/2.09    ( ! [X14,X12,X13] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X14))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f894,f569])).
% 13.19/2.09  fof(f894,plain,(
% 13.19/2.09    ( ! [X14,X12,X13] : (k3_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X13,X14)) = k4_xboole_0(k1_xboole_0,X14)) )),
% 13.19/2.09    inference(superposition,[],[f94,f881])).
% 13.19/2.09  fof(f1154,plain,(
% 13.19/2.09    ( ! [X26,X24,X25] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X24,X25),X26),X25)) )),
% 13.19/2.09    inference(resolution,[],[f1136,f75])).
% 13.19/2.09  fof(f75,plain,(
% 13.19/2.09    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f13])).
% 13.19/2.09  fof(f13,axiom,(
% 13.19/2.09    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 13.19/2.09  fof(f81,plain,(
% 13.19/2.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 13.19/2.09    inference(cnf_transformation,[],[f14])).
% 13.19/2.09  fof(f14,axiom,(
% 13.19/2.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 13.19/2.09  fof(f19929,plain,(
% 13.19/2.09    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2) )),
% 13.19/2.09    inference(resolution,[],[f19859,f86])).
% 13.19/2.09  fof(f19859,plain,(
% 13.19/2.09    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 13.19/2.09    inference(superposition,[],[f74,f18594])).
% 13.19/2.09  fof(f18594,plain,(
% 13.19/2.09    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(X6,k2_xboole_0(X5,X6))) )),
% 13.19/2.09    inference(superposition,[],[f13915,f77])).
% 13.19/2.09  fof(f13915,plain,(
% 13.19/2.09    ( ! [X33,X32] : (k2_xboole_0(X33,X32) = k2_xboole_0(k2_xboole_0(X33,X32),X32)) )),
% 13.19/2.09    inference(forward_demodulation,[],[f13914,f585])).
% 13.19/2.09  fof(f13914,plain,(
% 13.19/2.09    ( ! [X33,X32] : (k2_xboole_0(k2_xboole_0(X33,X32),X32) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X33,X32))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f13751,f77])).
% 13.19/2.09  fof(f13751,plain,(
% 13.19/2.09    ( ! [X33,X32] : (k2_xboole_0(k2_xboole_0(X33,X32),X32) = k2_xboole_0(k2_xboole_0(X33,X32),k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f81,f13441])).
% 13.19/2.09  fof(f13441,plain,(
% 13.19/2.09    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 13.19/2.09    inference(superposition,[],[f13310,f77])).
% 13.19/2.09  fof(f22356,plain,(
% 13.19/2.09    ( ! [X165,X164] : (r1_tarski(k3_xboole_0(X165,X164),X164)) )),
% 13.19/2.09    inference(superposition,[],[f19859,f22158])).
% 13.19/2.09  fof(f22158,plain,(
% 13.19/2.09    ( ! [X8,X7] : (k2_xboole_0(X8,k3_xboole_0(X7,X8)) = X8) )),
% 13.19/2.09    inference(forward_demodulation,[],[f21919,f604])).
% 13.19/2.09  fof(f21919,plain,(
% 13.19/2.09    ( ! [X8,X7] : (k2_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k3_xboole_0(X7,X8))) )),
% 13.19/2.09    inference(superposition,[],[f81,f21645])).
% 13.19/2.09  fof(f21645,plain,(
% 13.19/2.09    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X6)) )),
% 13.19/2.09    inference(superposition,[],[f20190,f2062])).
% 13.19/2.09  fof(f2062,plain,(
% 13.19/2.09    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 13.19/2.09    inference(superposition,[],[f1173,f95])).
% 13.19/2.09  fof(f1173,plain,(
% 13.19/2.09    ( ! [X6,X4,X5] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k4_xboole_0(X4,X5),X6),X5)) )),
% 13.19/2.09    inference(resolution,[],[f1152,f797])).
% 13.19/2.09  fof(f1152,plain,(
% 13.19/2.09    ( ! [X19,X20,X18] : (r1_xboole_0(k3_xboole_0(k4_xboole_0(X18,X19),X20),X19)) )),
% 13.19/2.09    inference(resolution,[],[f1136,f76])).
% 13.19/2.09  fof(f20190,plain,(
% 13.19/2.09    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k3_xboole_0(k4_xboole_0(X15,X16),X15)) )),
% 13.19/2.09    inference(superposition,[],[f19929,f3975])).
% 13.19/2.09  fof(f3975,plain,(
% 13.19/2.09    ( ! [X39,X38] : (k2_xboole_0(X38,k4_xboole_0(X38,X39)) = X38) )),
% 13.19/2.09    inference(forward_demodulation,[],[f3904,f604])).
% 13.19/2.09  fof(f3904,plain,(
% 13.19/2.09    ( ! [X39,X38] : (k2_xboole_0(X38,k4_xboole_0(X38,X39)) = k2_xboole_0(X38,k1_xboole_0)) )),
% 13.19/2.09    inference(superposition,[],[f81,f3839])).
% 13.19/2.09  fof(f3839,plain,(
% 13.19/2.09    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 13.19/2.09    inference(forward_demodulation,[],[f3811,f3783])).
% 13.19/2.09  fof(f3783,plain,(
% 13.19/2.09    ( ! [X10,X8,X9] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(k4_xboole_0(X8,X9),X8),X10)) )),
% 13.19/2.09    inference(resolution,[],[f3754,f797])).
% 13.19/2.09  fof(f3754,plain,(
% 13.19/2.09    ( ! [X24,X23,X22] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X22,X23),X22),X24)) )),
% 13.19/2.09    inference(resolution,[],[f3034,f1265])).
% 13.19/2.09  fof(f1265,plain,(
% 13.19/2.09    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X2,X3)) )),
% 13.19/2.09    inference(superposition,[],[f1153,f72])).
% 13.19/2.09  fof(f1153,plain,(
% 13.19/2.09    ( ! [X23,X21,X22] : (r1_xboole_0(k3_xboole_0(X21,X22),X23) | ~r1_xboole_0(X21,X22)) )),
% 13.19/2.09    inference(resolution,[],[f1136,f755])).
% 13.19/2.09  fof(f3034,plain,(
% 13.19/2.09    ( ! [X35,X33,X34,X32] : (r1_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k4_xboole_0(X33,X34),X35))) )),
% 13.19/2.09    inference(forward_demodulation,[],[f3010,f615])).
% 13.19/2.09  fof(f3010,plain,(
% 13.19/2.09    ( ! [X35,X33,X34,X32] : (r1_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(k4_xboole_0(k4_xboole_0(X33,X34),k1_xboole_0),X35))) )),
% 13.19/2.09    inference(superposition,[],[f2751,f899])).
% 13.19/2.09  fof(f2751,plain,(
% 13.19/2.09    ( ! [X52,X50,X51] : (r1_xboole_0(X50,k4_xboole_0(k4_xboole_0(X51,k3_xboole_0(X50,X51)),X52))) )),
% 13.19/2.09    inference(superposition,[],[f1306,f2381])).
% 13.19/2.09  fof(f1306,plain,(
% 13.19/2.09    ( ! [X17,X18,X16] : (r1_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18))) )),
% 13.19/2.09    inference(subsumption_resolution,[],[f1296,f472])).
% 13.19/2.09  fof(f1296,plain,(
% 13.19/2.09    ( ! [X17,X18,X16] : (r2_hidden(sK3(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18)),k1_xboole_0) | r1_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X18))) )),
% 13.19/2.09    inference(superposition,[],[f83,f899])).
% 13.19/2.09  fof(f3811,plain,(
% 13.19/2.09    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),X3) = k3_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X3),X5)) )),
% 13.19/2.09    inference(resolution,[],[f3755,f86])).
% 13.19/2.09  fof(f3755,plain,(
% 13.19/2.09    ( ! [X26,X27,X25] : (r1_tarski(k4_xboole_0(k4_xboole_0(X25,X26),X25),X27)) )),
% 13.19/2.09    inference(resolution,[],[f3034,f801])).
% 13.19/2.09  fof(f28814,plain,(
% 13.19/2.09    ( ! [X14,X15] : (k3_xboole_0(X14,X15) = k3_xboole_0(X15,X14) | ~r1_tarski(k3_xboole_0(X15,X14),k3_xboole_0(X14,X15))) )),
% 13.19/2.09    inference(resolution,[],[f28333,f89])).
% 13.19/2.09  fof(f89,plain,(
% 13.19/2.09    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 13.19/2.09    inference(cnf_transformation,[],[f55])).
% 13.19/2.09  fof(f55,plain,(
% 13.19/2.09    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.19/2.09    inference(flattening,[],[f54])).
% 13.19/2.09  fof(f54,plain,(
% 13.19/2.09    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 13.19/2.09    inference(nnf_transformation,[],[f5])).
% 13.19/2.09  fof(f5,axiom,(
% 13.19/2.09    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.19/2.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.19/2.09  % SZS output end Proof for theBenchmark
% 13.19/2.09  % (8090)------------------------------
% 13.19/2.09  % (8090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.19/2.09  % (8090)Termination reason: Refutation
% 13.19/2.09  
% 13.19/2.09  % (8090)Memory used [KB]: 12792
% 13.19/2.09  % (8090)Time elapsed: 1.618 s
% 13.19/2.09  % (8090)------------------------------
% 13.19/2.09  % (8090)------------------------------
% 13.25/2.09  % (8066)Success in time 1.721 s
%------------------------------------------------------------------------------
