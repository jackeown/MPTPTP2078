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
% DateTime   : Thu Dec  3 12:54:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 403 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   19
%              Number of atoms          :  249 (1694 expanded)
%              Number of equality atoms :   52 ( 346 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f51,f53,f247])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f221,f241])).

fof(f241,plain,(
    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f240,f235])).

fof(f235,plain,(
    r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f228,f146])).

fof(f146,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f45])).

fof(f45,plain,
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

fof(f24,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f145,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f143,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f143,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f142,f49])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f141,f50])).

fof(f50,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f141,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f125,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f125,plain,(
    ! [X5] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | r1_tarski(k9_relat_1(sK1,X5),k1_relat_1(k2_funct_1(sK1))) ) ),
    inference(superposition,[],[f65,f115])).

fof(f115,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f114,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f228,plain,
    ( r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1)))
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f121,f225])).

fof(f225,plain,(
    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(subsumption_resolution,[],[f224,f49])).

fof(f224,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f223,f50])).

fof(f223,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f134,f59])).

fof(f134,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(superposition,[],[f133,f57])).

fof(f133,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f121,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X2))
      | ~ r1_tarski(k2_relat_1(sK1),X2) ) ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f118,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X2))
      | ~ r1_tarski(k2_relat_1(sK1),X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f75,f110])).

fof(f110,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f109,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f105,f65])).

fof(f105,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k1_relat_1(sK1))
    | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f104,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f104,plain,(
    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f102,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f99,f57])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f240,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f239,f74])).

fof(f239,plain,(
    r1_tarski(k2_relat_1(k2_funct_1(sK1)),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f238,f110])).

fof(f238,plain,(
    r1_tarski(k2_relat_1(k2_funct_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f233,f49])).

fof(f233,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f66,f225])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f221,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(k2_funct_1(sK1))) ) ),
    inference(forward_demodulation,[],[f220,f115])).

fof(f220,plain,(
    ! [X0] :
      ( k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(k2_funct_1(sK1))) ) ),
    inference(forward_demodulation,[],[f219,f133])).

fof(f219,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(k2_funct_1(sK1))) ) ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f217,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(k2_funct_1(sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f140,f50])).

fof(f140,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X1)) = X1
      | ~ r1_tarski(X1,k2_relat_1(k2_funct_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f138,f59])).

fof(f138,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_funct_1(X2)))
      | k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X1)) = X1
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f71,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f53,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.43  % (26443)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.46  % (26467)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.47  % (26459)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.47  % (26451)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.49  % (26462)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.49  % (26444)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.49  % (26454)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (26441)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (26446)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (26445)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.52  % (26442)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (26465)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.52  % (26462)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f288,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f51,f53,f247])).
% 0.19/0.52  fof(f247,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 0.19/0.52    inference(backward_demodulation,[],[f221,f241])).
% 0.19/0.52  fof(f241,plain,(
% 0.19/0.52    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1))),
% 0.19/0.52    inference(subsumption_resolution,[],[f240,f235])).
% 0.19/0.52  fof(f235,plain,(
% 0.19/0.52    r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f228,f146])).
% 0.19/0.52  fof(f146,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f145,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    v1_relat_1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.52    inference(negated_conjecture,[],[f21])).
% 0.19/0.52  fof(f21,conjecture,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.19/0.52  fof(f145,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(superposition,[],[f143,f57])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.19/0.52  fof(f143,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f142,f49])).
% 0.19/0.52  fof(f142,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f141,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    v1_funct_1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f46])).
% 0.19/0.52  fof(f141,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f125,f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.52  fof(f125,plain,(
% 0.19/0.52    ( ! [X5] : (~v1_relat_1(k2_funct_1(sK1)) | r1_tarski(k9_relat_1(sK1,X5),k1_relat_1(k2_funct_1(sK1)))) )),
% 0.19/0.52    inference(superposition,[],[f65,f115])).
% 0.19/0.52  fof(f115,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f114,f49])).
% 0.19/0.52  fof(f114,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f113,f50])).
% 0.19/0.52  fof(f113,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f69,f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    v2_funct_1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f46])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.19/0.52  fof(f228,plain,(
% 0.19/0.52    r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1))) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(superposition,[],[f121,f225])).
% 0.19/0.52  fof(f225,plain,(
% 0.19/0.52    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f224,f49])).
% 0.19/0.52  fof(f224,plain,(
% 0.19/0.52    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f223,f50])).
% 0.19/0.52  fof(f223,plain,(
% 0.19/0.52    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(resolution,[],[f134,f59])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    ~v1_relat_1(k2_funct_1(sK1)) | k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(superposition,[],[f133,f57])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f132,f49])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f131,f50])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f70,f52])).
% 0.19/0.52  fof(f70,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    ( ! [X2] : (r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X2)) | ~r1_tarski(k2_relat_1(sK1),X2)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f118,f49])).
% 0.19/0.52  fof(f118,plain,(
% 0.19/0.52    ( ! [X2] : (r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X2)) | ~r1_tarski(k2_relat_1(sK1),X2) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(superposition,[],[f75,f110])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.19/0.52    inference(subsumption_resolution,[],[f109,f49])).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(resolution,[],[f105,f65])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k1_relat_1(sK1)) | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.19/0.52    inference(resolution,[],[f104,f74])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(flattening,[],[f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.52  fof(f104,plain,(
% 0.19/0.52    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f103,f49])).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f102,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.52    inference(equality_resolution,[],[f73])).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f48])).
% 0.19/0.52  fof(f102,plain,(
% 0.19/0.52    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(superposition,[],[f99,f57])).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.19/0.52    inference(resolution,[],[f67,f49])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.19/0.52  fof(f75,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.52    inference(flattening,[],[f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.19/0.52  fof(f240,plain,(
% 0.19/0.52    k1_relat_1(sK1) = k2_relat_1(k2_funct_1(sK1)) | ~r1_tarski(k1_relat_1(sK1),k2_relat_1(k2_funct_1(sK1)))),
% 0.19/0.52    inference(resolution,[],[f239,f74])).
% 0.19/0.52  fof(f239,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(k2_funct_1(sK1)),k1_relat_1(sK1))),
% 0.19/0.52    inference(forward_demodulation,[],[f238,f110])).
% 0.19/0.52  fof(f238,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(k2_funct_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 0.19/0.52    inference(subsumption_resolution,[],[f233,f49])).
% 0.19/0.52  fof(f233,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(k2_funct_1(sK1)),k10_relat_1(sK1,k2_relat_1(sK1))) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(superposition,[],[f66,f225])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 0.19/0.52  fof(f221,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(k2_funct_1(sK1)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f220,f115])).
% 0.19/0.52  fof(f220,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~r1_tarski(X0,k2_relat_1(k2_funct_1(sK1)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f219,f133])).
% 0.19/0.52  fof(f219,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~r1_tarski(X0,k2_relat_1(k2_funct_1(sK1)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f217,f49])).
% 0.19/0.52  fof(f217,plain,(
% 0.19/0.52    ( ! [X0] : (k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),X0)) = X0 | ~r1_tarski(X0,k2_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f140,f50])).
% 0.19/0.52  fof(f140,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~v1_funct_1(X2) | k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X1)) = X1 | ~r1_tarski(X1,k2_relat_1(k2_funct_1(X2))) | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f138,f59])).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(k2_funct_1(X2))) | k9_relat_1(k2_funct_1(X2),k10_relat_1(k2_funct_1(X2),X1)) = X1 | ~v1_relat_1(k2_funct_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.19/0.52    inference(resolution,[],[f71,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f46])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.52    inference(cnf_transformation,[],[f46])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (26462)------------------------------
% 0.19/0.52  % (26462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (26462)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (26462)Memory used [KB]: 6396
% 0.19/0.52  % (26462)Time elapsed: 0.079 s
% 0.19/0.52  % (26462)------------------------------
% 0.19/0.52  % (26462)------------------------------
% 0.19/0.52  % (26468)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.52  % (26468)Refutation not found, incomplete strategy% (26468)------------------------------
% 0.19/0.52  % (26468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (26468)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (26468)Memory used [KB]: 10746
% 0.19/0.52  % (26468)Time elapsed: 0.139 s
% 0.19/0.52  % (26468)------------------------------
% 0.19/0.52  % (26468)------------------------------
% 0.19/0.53  % (26438)Success in time 0.186 s
%------------------------------------------------------------------------------
