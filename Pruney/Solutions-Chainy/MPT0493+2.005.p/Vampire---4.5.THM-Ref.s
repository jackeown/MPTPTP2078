%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 231 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  206 ( 856 expanded)
%              Number of equality atoms :   58 ( 226 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31463)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f127,f316])).

fof(f316,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f295,f25])).

fof(f25,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

% (31442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f16,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f295,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f104,f290])).

fof(f290,plain,
    ( ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f283,f40])).

fof(f40,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f283,plain,
    ( ! [X1] : k1_setfam_1(k2_tarski(X1,X1)) = k4_xboole_0(X1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f41,f272])).

fof(f272,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_4 ),
    inference(superposition,[],[f254,f40])).

fof(f254,plain,
    ( ! [X6,X7] : k1_xboole_0 = k1_setfam_1(k2_tarski(k4_xboole_0(X6,X6),X7))
    | ~ spl3_4 ),
    inference(superposition,[],[f247,f41])).

fof(f247,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f241,f153])).

fof(f153,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X8)
        | r2_hidden(sK2(k4_xboole_0(X6,X7),X8,k1_xboole_0),X6) )
    | ~ spl3_4 ),
    inference(resolution,[],[f145,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f145,plain,
    ( ! [X21,X22] :
        ( r2_hidden(sK2(X21,X22,k1_xboole_0),X21)
        | k1_xboole_0 = k4_xboole_0(X21,X22) )
    | ~ spl3_4 ),
    inference(resolution,[],[f37,f122])).

fof(f122,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(k4_xboole_0(X0,X0),X1,k1_xboole_0),X0)
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1) )
    | ~ spl3_4 ),
    inference(superposition,[],[f170,f40])).

fof(f170,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK2(k4_xboole_0(X3,X4),X5,k1_xboole_0),k1_setfam_1(k2_tarski(X3,X4)))
        | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X5) )
    | ~ spl3_4 ),
    inference(superposition,[],[f152,f41])).

fof(f152,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK2(X3,X4,k1_xboole_0),k4_xboole_0(X5,X3))
        | k1_xboole_0 = k4_xboole_0(X3,X4) )
    | ~ spl3_4 ),
    inference(resolution,[],[f145,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f104,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f90,f58])).

fof(f58,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = k4_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f90,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f89,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f127,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f119,f24])).

fof(f119,plain,
    ( ! [X0] : ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_3
  <=> ! [X0] : ~ r1_tarski(X0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f123,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f116,f121,f118])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f115,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f52,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f59,f73])).

fof(f73,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f59,f40])).

fof(f59,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0)))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f50,f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f45,f41])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f114,f33])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(X5,k1_relat_1(sK1)))
      | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4))) ) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X2))) ) ),
    inference(superposition,[],[f50,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (31444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (31444)Refutation not found, incomplete strategy% (31444)------------------------------
% 0.20/0.50  % (31444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31444)Memory used [KB]: 6140
% 0.20/0.50  % (31444)Time elapsed: 0.092 s
% 0.20/0.50  % (31444)------------------------------
% 0.20/0.50  % (31444)------------------------------
% 0.20/0.51  % (31462)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (31454)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (31445)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (31452)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31446)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (31443)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (31450)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (31460)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (31450)Refutation not found, incomplete strategy% (31450)------------------------------
% 0.20/0.52  % (31450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31450)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31450)Memory used [KB]: 10618
% 0.20/0.52  % (31450)Time elapsed: 0.117 s
% 0.20/0.52  % (31450)------------------------------
% 0.20/0.52  % (31450)------------------------------
% 0.20/0.52  % (31440)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (31440)Refutation not found, incomplete strategy% (31440)------------------------------
% 0.20/0.52  % (31440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31440)Memory used [KB]: 1663
% 0.20/0.52  % (31440)Time elapsed: 0.116 s
% 0.20/0.52  % (31440)------------------------------
% 0.20/0.52  % (31440)------------------------------
% 0.20/0.52  % (31447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (31441)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (31462)Refutation not found, incomplete strategy% (31462)------------------------------
% 0.20/0.52  % (31462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31456)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (31459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (31457)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (31457)Refutation not found, incomplete strategy% (31457)------------------------------
% 0.20/0.52  % (31457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31457)Memory used [KB]: 10618
% 0.20/0.52  % (31457)Time elapsed: 0.130 s
% 0.20/0.52  % (31457)------------------------------
% 0.20/0.52  % (31457)------------------------------
% 0.20/0.53  % (31462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31462)Memory used [KB]: 10618
% 0.20/0.53  % (31462)Time elapsed: 0.069 s
% 0.20/0.53  % (31462)------------------------------
% 0.20/0.53  % (31462)------------------------------
% 0.20/0.53  % (31448)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (31469)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (31464)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (31451)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (31467)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (31465)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (31443)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  % (31463)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f123,f127,f316])).
% 0.20/0.53  fof(f316,plain,(
% 0.20/0.53    ~spl3_4),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f315])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    $false | ~spl3_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f295,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  % (31442)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_4),
% 0.20/0.53    inference(backward_demodulation,[],[f104,f290])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl3_4),
% 0.20/0.53    inference(forward_demodulation,[],[f283,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f27,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    ( ! [X1] : (k1_setfam_1(k2_tarski(X1,X1)) = k4_xboole_0(X1,k1_xboole_0)) ) | ~spl3_4),
% 0.20/0.53    inference(superposition,[],[f41,f272])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl3_4),
% 0.20/0.53    inference(superposition,[],[f254,f40])).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    ( ! [X6,X7] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k4_xboole_0(X6,X6),X7))) ) | ~spl3_4),
% 0.20/0.53    inference(superposition,[],[f247,f41])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) ) | ~spl3_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f241,f153])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X8) | r2_hidden(sK2(k4_xboole_0(X6,X7),X8,k1_xboole_0),X6)) ) | ~spl3_4),
% 0.20/0.53    inference(resolution,[],[f145,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X21,X22] : (r2_hidden(sK2(X21,X22,k1_xboole_0),X21) | k1_xboole_0 = k4_xboole_0(X21,X22)) ) | ~spl3_4),
% 0.20/0.53    inference(resolution,[],[f37,f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    spl3_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X0),X1,k1_xboole_0),X0) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X0),X1)) ) | ~spl3_4),
% 0.20/0.53    inference(superposition,[],[f170,f40])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~r2_hidden(sK2(k4_xboole_0(X3,X4),X5,k1_xboole_0),k1_setfam_1(k2_tarski(X3,X4))) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X5)) ) | ~spl3_4),
% 0.20/0.53    inference(superposition,[],[f152,f41])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X3,X4,k1_xboole_0),k4_xboole_0(X5,X3)) | k1_xboole_0 = k4_xboole_0(X3,X4)) ) | ~spl3_4),
% 0.20/0.53    inference(resolution,[],[f145,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f30,f29])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    k1_relat_1(k7_relat_1(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f90,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f47,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f41,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 0.20/0.53    inference(superposition,[],[f89,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 0.20/0.53    inference(resolution,[],[f42,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f31,f29])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~spl3_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    $false | ~spl3_3),
% 0.20/0.53    inference(resolution,[],[f119,f24])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl3_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl3_3 <=> ! [X0] : ~r1_tarski(X0,k1_relat_1(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    spl3_3 | spl3_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f116,f121,f118])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f115,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(superposition,[],[f52,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(backward_demodulation,[],[f59,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f59,f40])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0] : (k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.53    inference(resolution,[],[f47,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X1,X0))) | r2_hidden(X2,X0)) )),
% 0.20/0.53    inference(superposition,[],[f50,f28])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X2,X0)) )),
% 0.20/0.53    inference(superposition,[],[f45,f41])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(sK1,X2))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.20/0.53    inference(superposition,[],[f114,f33])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X4,X5,X3] : (~r2_hidden(X3,k4_xboole_0(X5,k1_relat_1(sK1))) | ~r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X4)))) )),
% 0.20/0.53    inference(resolution,[],[f96,f44])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X3] : (r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 0.20/0.53    inference(superposition,[],[f50,f89])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (31443)------------------------------
% 0.20/0.53  % (31443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31443)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (31443)Memory used [KB]: 10874
% 0.20/0.53  % (31443)Time elapsed: 0.116 s
% 0.20/0.53  % (31443)------------------------------
% 0.20/0.53  % (31443)------------------------------
% 0.20/0.53  % (31435)Success in time 0.174 s
%------------------------------------------------------------------------------
