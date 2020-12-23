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
% DateTime   : Thu Dec  3 13:07:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 295 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          :  182 ( 494 expanded)
%              Number of equality atoms :   72 ( 261 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f73,f78,f139,f316,f398])).

fof(f398,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f396,f77])).

fof(f77,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f396,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f394,f143])).

fof(f143,plain,
    ( ! [X2] : k10_relat_1(sK0,X2) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X2)),X2)
    | ~ spl3_1 ),
    inference(superposition,[],[f91,f54])).

fof(f54,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f91,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f62,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f394,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(superposition,[],[f259,f315])).

fof(f315,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl3_8
  <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f259,plain,
    ( ! [X4,X3] : k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X3),X4)),X4)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f258,f84])).

fof(f84,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f62,f57,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f258,plain,
    ( ! [X4,X3] : k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X3),X4)),X4)
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f254,f256])).

fof(f256,plain,
    ( ! [X4,X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),k10_relat_1(k7_relat_1(sK0,X3),X4)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X2),X4))
    | ~ spl3_1 ),
    inference(superposition,[],[f96,f92])).

fof(f92,plain,
    ( ! [X2,X0,X1] : k10_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1),X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(k7_relat_1(sK0,X0),X2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f79,f55])).

fof(f79,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK0,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (11509)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f96,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f62,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f254,plain,
    ( ! [X4,X3] : k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),k10_relat_1(k7_relat_1(sK0,X3),X4)),X4)
    | ~ spl3_1 ),
    inference(superposition,[],[f92,f54])).

fof(f316,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f210,f136,f60,f313])).

fof(f136,plain,
    ( spl3_7
  <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f210,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f156,f138])).

fof(f138,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f156,plain,
    ( ! [X2,X1] : k7_relat_1(k7_relat_1(sK0,X1),k10_relat_1(sK0,X2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X1),X2))
    | ~ spl3_1 ),
    inference(superposition,[],[f96,f91])).

fof(f139,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f86,f70,f60,f136])).

fof(f70,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f86,plain,
    ( k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f62,f72,f43])).

fof(f72,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f78,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f73,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 17:13:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.51  % (11520)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (11528)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (11516)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (11515)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (11530)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (11523)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (11514)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (11532)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (11524)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (11537)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (11524)Refutation not found, incomplete strategy% (11524)------------------------------
% 0.22/0.53  % (11524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11524)Memory used [KB]: 10618
% 0.22/0.53  % (11524)Time elapsed: 0.125 s
% 0.22/0.53  % (11524)------------------------------
% 0.22/0.53  % (11524)------------------------------
% 0.22/0.53  % (11531)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (11517)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (11512)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (11513)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11511)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (11536)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (11536)Refutation not found, incomplete strategy% (11536)------------------------------
% 0.22/0.54  % (11536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11536)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11536)Memory used [KB]: 10746
% 0.22/0.54  % (11536)Time elapsed: 0.126 s
% 0.22/0.54  % (11536)------------------------------
% 0.22/0.54  % (11536)------------------------------
% 0.22/0.54  % (11522)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (11529)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (11527)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (11528)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f400,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f63,f73,f78,f139,f316,f398])).
% 0.22/0.55  fof(f398,plain,(
% 0.22/0.55    ~spl3_1 | spl3_4 | ~spl3_8),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f397])).
% 0.22/0.55  fof(f397,plain,(
% 0.22/0.55    $false | (~spl3_1 | spl3_4 | ~spl3_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f396,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    spl3_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f396,plain,(
% 0.22/0.55    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_1 | ~spl3_8)),
% 0.22/0.55    inference(forward_demodulation,[],[f394,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X2] : (k10_relat_1(sK0,X2) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X2)),X2)) ) | ~spl3_1),
% 0.22/0.55    inference(superposition,[],[f91,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f33,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f34,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f35,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f40,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f44,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f45,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f46,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.55    inference(rectify,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl3_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f41,f53])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    v1_relat_1(sK0) | ~spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    spl3_1 <=> v1_relat_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f394,plain,(
% 0.22/0.55    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,sK2)),sK2) | (~spl3_1 | ~spl3_8)),
% 0.22/0.55    inference(superposition,[],[f259,f315])).
% 0.22/0.55  fof(f315,plain,(
% 0.22/0.55    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | ~spl3_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f313])).
% 0.22/0.55  fof(f313,plain,(
% 0.22/0.55    spl3_8 <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X3),X4)),X4)) ) | ~spl3_1),
% 0.22/0.55    inference(forward_demodulation,[],[f258,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)) ) | ~spl3_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f57,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(sK0,k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X3),X4)),X4)) ) | ~spl3_1),
% 0.22/0.55    inference(backward_demodulation,[],[f254,f256])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(sK0,X2),k10_relat_1(k7_relat_1(sK0,X3),X4)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),X2),X4))) ) | ~spl3_1),
% 0.22/0.55    inference(superposition,[],[f96,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1),X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(k7_relat_1(sK0,X0),X2)))) ) | ~spl3_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f79,f55])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl3_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % (11509)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl3_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f42,f53])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.55  fof(f254,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK0,X3),X4) = k10_relat_1(k7_relat_1(k7_relat_1(sK0,X3),k10_relat_1(k7_relat_1(sK0,X3),X4)),X4)) ) | ~spl3_1),
% 0.22/0.55    inference(superposition,[],[f92,f54])).
% 0.22/0.55  fof(f316,plain,(
% 0.22/0.55    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f210,f136,f60,f313])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    spl3_7 <=> k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,sK1),sK2)) | (~spl3_1 | ~spl3_7)),
% 0.22/0.55    inference(superposition,[],[f156,f138])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | ~spl3_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f136])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK0,X1),k10_relat_1(sK0,X2)) = k7_relat_1(sK0,k10_relat_1(k7_relat_1(sK0,X1),X2))) ) | ~spl3_1),
% 0.22/0.55    inference(superposition,[],[f96,f91])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    spl3_7 | ~spl3_1 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f86,f70,f60,f136])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    k7_relat_1(sK0,k10_relat_1(sK0,sK2)) = k7_relat_1(k7_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) | (~spl3_1 | ~spl3_3)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f62,f72,f43])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f70])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ~spl3_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f32,f75])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f25,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.22/0.55    inference(negated_conjecture,[],[f14])).
% 0.22/0.55  fof(f14,conjecture,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f31,f70])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl3_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f29,f60])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    v1_relat_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (11528)------------------------------
% 0.22/0.55  % (11528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11528)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (11528)Memory used [KB]: 11129
% 0.22/0.55  % (11528)Time elapsed: 0.142 s
% 0.22/0.55  % (11528)------------------------------
% 0.22/0.55  % (11528)------------------------------
% 0.22/0.55  % (11507)Success in time 0.179 s
%------------------------------------------------------------------------------
