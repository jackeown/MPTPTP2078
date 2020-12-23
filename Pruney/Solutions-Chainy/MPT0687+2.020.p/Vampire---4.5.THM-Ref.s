%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 468 expanded)
%              Number of leaves         :   20 ( 118 expanded)
%              Depth                    :   27
%              Number of atoms          :  237 (1348 expanded)
%              Number of equality atoms :   97 ( 527 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f187,f205])).

fof(f205,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f203,f176])).

fof(f176,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f95,f175])).

fof(f175,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f174,f136])).

fof(f136,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f126,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f126,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f125,f60])).

fof(f60,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f125,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f121,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

fof(f121,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,k1_xboole_0)),X0) ),
    inference(resolution,[],[f117,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f117,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f116,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f69,f106])).

fof(f106,plain,(
    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f174,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(resolution,[],[f172,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f172,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f171,f60])).

fof(f171,plain,(
    ! [X1] : r1_xboole_0(k2_relat_1(k1_xboole_0),X1) ),
    inference(subsumption_resolution,[],[f167,f117])).

fof(f167,plain,(
    ! [X1] :
      ( r1_xboole_0(k2_relat_1(k1_xboole_0),X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f166])).

fof(f166,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_relat_1(k1_xboole_0),X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f74,f135])).

fof(f135,plain,(
    ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f134,f119])).

fof(f119,plain,(
    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f117,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f134,plain,(
    ! [X3] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f133,f132])).

fof(f132,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f131,f60])).

fof(f131,plain,(
    ! [X2] : k2_relat_1(k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f130,f61])).

fof(f130,plain,(
    ! [X2] : k2_relat_1(k8_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f123,f60])).

fof(f123,plain,(
    ! [X2] : k2_relat_1(k8_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X2)) ),
    inference(resolution,[],[f117,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f133,plain,(
    ! [X3] : k10_relat_1(k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) ),
    inference(forward_demodulation,[],[f124,f60])).

fof(f124,plain,(
    ! [X3] : k10_relat_1(k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X3))) ),
    inference(resolution,[],[f117,f91])).

% (15920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f73,f65])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f95,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f203,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f190,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)))
    | ~ spl3_2 ),
    inference(resolution,[],[f199,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f81,f65])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f199,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f195,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f74,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f190,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)))
    | ~ spl3_1 ),
    inference(resolution,[],[f98,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) ) ),
    inference(definition_unfolding,[],[f80,f65])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f98,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f187,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f182,f102])).

fof(f102,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f182,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f181,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f181,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f179,f175])).

fof(f179,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_1 ),
    inference(superposition,[],[f93,f114])).

fof(f114,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_1 ),
    inference(resolution,[],[f99,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f99,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f65])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f101,f97])).

fof(f57,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f58,f101,f97])).

fof(f58,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (15912)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (15912)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f104,f105,f187,f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f203,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f95,f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f174,f136])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.49    inference(resolution,[],[f126,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f121,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,k1_xboole_0)),X0)) )),
% 0.21/0.49    inference(resolution,[],[f117,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f23])).
% 0.21/0.49  fof(f23,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f69,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f56,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)) )),
% 0.21/0.49    inference(resolution,[],[f172,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f171,f60])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X1] : (r1_xboole_0(k2_relat_1(k1_xboole_0),X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f117])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X1] : (r1_xboole_0(k2_relat_1(k1_xboole_0),X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(k1_xboole_0),X1) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.49    inference(superposition,[],[f74,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f117,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X3] : (k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f133,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f131,f60])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X2] : (k2_relat_1(k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f130,f61])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X2] : (k2_relat_1(k8_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f123,f60])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X2] : (k2_relat_1(k8_relat_1(X2,k1_xboole_0)) = k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X2))) )),
% 0.21/0.49    inference(resolution,[],[f117,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f72,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X3] : (k10_relat_1(k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f124,f60])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X3] : (k10_relat_1(k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),X3)))) )),
% 0.21/0.49    inference(resolution,[],[f117,f91])).
% 0.21/0.49  % (15920)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f73,f65])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    k1_xboole_0 = k1_tarski(sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.49    inference(backward_demodulation,[],[f190,f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))) | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f199,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f81,f65])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl3_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f195,f56])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.49    inference(superposition,[],[f74,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl3_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    k1_tarski(sK0) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f98,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f80,f65])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    $false | (spl3_1 | spl3_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f185,f56])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | (spl3_1 | spl3_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f182,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f181,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f175])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)) | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_1),
% 0.21/0.49    inference(superposition,[],[f93,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f99,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f82,f65])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f101,f97])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f101,f97])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15912)------------------------------
% 0.21/0.49  % (15912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15912)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15912)Memory used [KB]: 10746
% 0.21/0.49  % (15912)Time elapsed: 0.087 s
% 0.21/0.49  % (15912)------------------------------
% 0.21/0.49  % (15912)------------------------------
% 0.21/0.50  % (15903)Success in time 0.141 s
%------------------------------------------------------------------------------
