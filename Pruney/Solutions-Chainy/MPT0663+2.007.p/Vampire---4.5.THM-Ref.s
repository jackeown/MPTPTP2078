%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 291 expanded)
%              Number of leaves         :   14 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  166 ( 706 expanded)
%              Number of equality atoms :   35 ( 187 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(subsumption_resolution,[],[f240,f29])).

fof(f29,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
    & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)
      & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f240,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f239,f30])).

fof(f30,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f239,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f233,f32])).

fof(f32,plain,(
    k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,
    ( k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f49,f144])).

fof(f144,plain,(
    r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3))) ),
    inference(resolution,[],[f138,f112])).

fof(f112,plain,(
    sP0(sK4,sK2,sK3) ),
    inference(resolution,[],[f107,f103])).

fof(f103,plain,(
    r2_hidden(sK2,sK3) ),
    inference(forward_demodulation,[],[f101,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f101,plain,(
    r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3))) ),
    inference(resolution,[],[f100,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,k1_relat_1(X0))
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( r2_hidden(X0,k1_relat_1(X2))
        & r2_hidden(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f100,plain,(
    sP0(k6_relat_1(sK3),sK2,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f56,plain,(
    ! [X4,X2,X3] : sP1(X2,X3,k6_relat_1(X4)) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | sP1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f16,f20,f19])).

fof(f20,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f97,plain,
    ( sP0(k6_relat_1(sK3),sK2,k1_relat_1(sK4))
    | ~ sP1(k1_relat_1(sK4),sK2,k6_relat_1(sK3)) ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f94,plain,(
    r2_hidden(sK2,k1_relat_1(k7_relat_1(k6_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    sP0(k7_relat_1(k6_relat_1(sK3),k1_relat_1(sK4)),sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f62,f66])).

fof(f66,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f54,f58])).

fof(f58,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f41,f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f62,plain,(
    sP0(k6_relat_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))),sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))) ),
    inference(resolution,[],[f61,f60])).

fof(f60,plain,(
    r2_hidden(sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))) ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f50,f50])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    r2_hidden(sK2,k1_setfam_1(k2_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3))) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f31,plain,(
    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sP0(k6_relat_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))),sK2,X0) ) ),
    inference(resolution,[],[f59,f60])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | sP0(k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sP0(sK4,sK2,X0) ) ),
    inference(resolution,[],[f102,f47])).

fof(f102,plain,(
    r2_hidden(sK2,k1_relat_1(sK4)) ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK4,X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,X1))) ) ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,(
    ! [X0,X1] : sP1(X0,X1,sK4) ),
    inference(resolution,[],[f48,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (31909)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.42  % (31909)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f241,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f240,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    v1_relat_1(sK4)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2) & r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f11])).
% 0.20/0.42  fof(f11,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).
% 0.20/0.42  fof(f240,plain,(
% 0.20/0.42    ~v1_relat_1(sK4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f239,f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    v1_funct_1(sK4)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f239,plain,(
% 0.20/0.42    ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.42    inference(subsumption_resolution,[],[f233,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k1_funct_1(k7_relat_1(sK4,sK3),sK2) != k1_funct_1(sK4,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f233,plain,(
% 0.20/0.42    k1_funct_1(k7_relat_1(sK4,sK3),sK2) = k1_funct_1(sK4,sK2) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.20/0.42    inference(resolution,[],[f49,f144])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_relat_1(k7_relat_1(sK4,sK3)))),
% 0.20/0.42    inference(resolution,[],[f138,f112])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    sP0(sK4,sK2,sK3)),
% 0.20/0.42    inference(resolution,[],[f107,f103])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    r2_hidden(sK2,sK3)),
% 0.20/0.42    inference(forward_demodulation,[],[f101,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.42  fof(f101,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_relat_1(k6_relat_1(sK3)))),
% 0.20/0.42    inference(resolution,[],[f100,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,k1_relat_1(X0)) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.20/0.42    inference(rectify,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP0(X2,X0,X1)))),
% 0.20/0.42    inference(flattening,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP0(X2,X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)))),
% 0.20/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    sP0(k6_relat_1(sK3),sK2,k1_relat_1(sK4))),
% 0.20/0.42    inference(subsumption_resolution,[],[f97,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X4,X2,X3] : (sP1(X2,X3,k6_relat_1(X4))) )),
% 0.20/0.42    inference(resolution,[],[f48,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | sP1(X1,X0,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(definition_folding,[],[f16,f20,f19])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X1,X0,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.20/0.42    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    sP0(k6_relat_1(sK3),sK2,k1_relat_1(sK4)) | ~sP1(k1_relat_1(sK4),sK2,k6_relat_1(sK3))),
% 0.20/0.42    inference(resolution,[],[f94,f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))))) | ~sP1(X0,X1,X2))),
% 0.20/0.42    inference(rectify,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X1,X0,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~sP1(X1,X0,X2))),
% 0.20/0.42    inference(nnf_transformation,[],[f20])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_relat_1(k7_relat_1(k6_relat_1(sK3),k1_relat_1(sK4))))),
% 0.20/0.42    inference(resolution,[],[f67,f46])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    sP0(k7_relat_1(k6_relat_1(sK3),k1_relat_1(sK4)),sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4))))),
% 0.20/0.42    inference(backward_demodulation,[],[f62,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.42    inference(forward_demodulation,[],[f54,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.20/0.42    inference(resolution,[],[f41,f33])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f40,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f39,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f38,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    sP0(k6_relat_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))),sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4))))),
% 0.20/0.42    inference(resolution,[],[f61,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4))))),
% 0.20/0.42    inference(backward_demodulation,[],[f52,f53])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f37,f50,f50])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_setfam_1(k2_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),sK3)))),
% 0.20/0.42    inference(definition_unfolding,[],[f31,f51])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    r2_hidden(sK2,k3_xboole_0(k1_relat_1(sK4),sK3))),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(sK2,X0) | sP0(k6_relat_1(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,k1_relat_1(sK4)))),sK2,X0)) )),
% 0.20/0.42    inference(resolution,[],[f59,f60])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | sP0(k6_relat_1(X0),X1,X2) | ~r2_hidden(X1,X2)) )),
% 0.20/0.42    inference(superposition,[],[f47,f35])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(sK2,X0) | sP0(sK4,sK2,X0)) )),
% 0.20/0.42    inference(resolution,[],[f102,f47])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    r2_hidden(sK2,k1_relat_1(sK4))),
% 0.20/0.42    inference(resolution,[],[f100,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f138,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~sP0(sK4,X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,X1)))) )),
% 0.20/0.42    inference(resolution,[],[f44,f55])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    ( ! [X0,X1] : (sP1(X0,X1,sK4)) )),
% 0.20/0.42    inference(resolution,[],[f48,f29])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (31909)------------------------------
% 0.20/0.42  % (31909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (31909)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (31909)Memory used [KB]: 1663
% 0.20/0.42  % (31909)Time elapsed: 0.010 s
% 0.20/0.42  % (31909)------------------------------
% 0.20/0.42  % (31909)------------------------------
% 0.20/0.43  % (31896)Success in time 0.067 s
%------------------------------------------------------------------------------
