%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:14 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 327 expanded)
%              Number of leaves         :   22 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  345 (1444 expanded)
%              Number of equality atoms :   70 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f272,f276,f284,f555])).

fof(f555,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f553,f50])).

fof(f50,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f553,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f549,f150])).

fof(f150,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f148,f138])).

fof(f138,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK2))) ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f61,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK2)))) ),
    inference(superposition,[],[f75,f87])).

fof(f87,plain,(
    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f60,f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f549,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f78,f520])).

fof(f520,plain,
    ( sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f519,f102])).

fof(f102,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_setfam_1(k2_tarski(X3,X4)))
      | k1_setfam_1(k2_tarski(X3,X4)) = X3 ) ),
    inference(resolution,[],[f68,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f519,plain,
    ( r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f518,f408])).

fof(f408,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f407,f250])).

fof(f250,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f249,f45])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f249,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f248,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f248,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f407,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f322,f280])).

fof(f280,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f279,f45])).

fof(f279,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f278,f46])).

fof(f278,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f322,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f321,f255])).

fof(f255,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f321,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f316,f259])).

fof(f259,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f316,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f299,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f299,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9 ),
    inference(resolution,[],[f296,f93])).

fof(f93,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK2),X2)
      | r1_tarski(sK0,X2) ) ),
    inference(superposition,[],[f71,f87])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f296,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9 ),
    inference(superposition,[],[f271,f94])).

fof(f94,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f271,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl3_9
  <=> ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f518,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f517,f45])).

fof(f517,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f516,f46])).

fof(f516,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f512,f49])).

fof(f512,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f62,f463])).

fof(f463,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f334,f136])).

fof(f136,plain,(
    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f334,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(subsumption_resolution,[],[f333,f45])).

fof(f333,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f332,f46])).

fof(f332,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f79,f49])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f72,f57,f57])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f284,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f282,f45])).

fof(f282,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f281,f46])).

fof(f281,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(resolution,[],[f260,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f260,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f258])).

fof(f276,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f274,f45])).

fof(f274,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f273,f46])).

fof(f273,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f256,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f256,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f254])).

fof(f272,plain,
    ( ~ spl3_5
    | spl3_9 ),
    inference(avatar_split_clause,[],[f252,f270,f254])).

fof(f252,plain,(
    ! [X1] :
      ( r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f59,f250])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.50/0.56  % (24920)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.57  % (24918)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.58  % (24919)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.58  % (24928)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.58  % (24931)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.58  % (24944)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.59  % (24926)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.59  % (24921)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.50/0.59  % (24942)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.59  % (24924)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.59  % (24928)Refutation not found, incomplete strategy% (24928)------------------------------
% 1.50/0.59  % (24928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (24923)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.60  % (24928)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (24928)Memory used [KB]: 10746
% 1.50/0.60  % (24928)Time elapsed: 0.158 s
% 1.50/0.60  % (24928)------------------------------
% 1.50/0.60  % (24928)------------------------------
% 1.50/0.60  % (24922)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.60  % (24945)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.61  % (24933)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.61  % (24943)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.61  % (24940)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.50/0.61  % (24937)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.61  % (24946)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.62  % (24947)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.62  % (24934)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.62  % (24947)Refutation not found, incomplete strategy% (24947)------------------------------
% 1.50/0.62  % (24947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (24947)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (24947)Memory used [KB]: 1663
% 1.50/0.62  % (24947)Time elapsed: 0.002 s
% 1.50/0.62  % (24947)------------------------------
% 1.50/0.62  % (24947)------------------------------
% 1.50/0.62  % (24927)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.62  % (24934)Refutation not found, incomplete strategy% (24934)------------------------------
% 1.50/0.62  % (24934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (24934)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (24934)Memory used [KB]: 10618
% 1.50/0.62  % (24934)Time elapsed: 0.181 s
% 1.50/0.62  % (24934)------------------------------
% 1.50/0.62  % (24934)------------------------------
% 1.50/0.62  % (24941)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.62  % (24938)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.62  % (24936)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.63  % (24930)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.63  % (24925)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.63  % (24939)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.63  % (24932)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.64  % (24946)Refutation not found, incomplete strategy% (24946)------------------------------
% 1.50/0.64  % (24946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.64  % (24946)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.64  
% 1.50/0.64  % (24946)Memory used [KB]: 10746
% 1.50/0.64  % (24946)Time elapsed: 0.200 s
% 1.50/0.64  % (24946)------------------------------
% 1.50/0.64  % (24946)------------------------------
% 1.50/0.64  % (24935)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.64  % (24924)Refutation found. Thanks to Tanya!
% 1.50/0.64  % SZS status Theorem for theBenchmark
% 1.50/0.64  % SZS output start Proof for theBenchmark
% 1.50/0.64  fof(f556,plain,(
% 1.50/0.64    $false),
% 1.50/0.64    inference(avatar_sat_refutation,[],[f272,f276,f284,f555])).
% 1.50/0.64  fof(f555,plain,(
% 1.50/0.64    ~spl3_5 | ~spl3_6 | ~spl3_9),
% 1.50/0.64    inference(avatar_contradiction_clause,[],[f554])).
% 1.50/0.64  fof(f554,plain,(
% 1.50/0.64    $false | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(subsumption_resolution,[],[f553,f50])).
% 1.50/0.64  fof(f50,plain,(
% 1.50/0.64    ~r1_tarski(sK0,sK1)),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f41,plain,(
% 1.50/0.64    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.50/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40])).
% 1.50/0.64  fof(f40,plain,(
% 1.50/0.64    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.50/0.64    introduced(choice_axiom,[])).
% 1.50/0.64  fof(f22,plain,(
% 1.50/0.64    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.50/0.64    inference(flattening,[],[f21])).
% 1.50/0.64  fof(f21,plain,(
% 1.50/0.64    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.50/0.64    inference(ennf_transformation,[],[f20])).
% 1.50/0.64  fof(f20,negated_conjecture,(
% 1.50/0.64    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.50/0.64    inference(negated_conjecture,[],[f19])).
% 1.50/0.64  fof(f19,conjecture,(
% 1.50/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.50/0.64  fof(f553,plain,(
% 1.50/0.64    r1_tarski(sK0,sK1) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(subsumption_resolution,[],[f549,f150])).
% 1.50/0.64  fof(f150,plain,(
% 1.50/0.64    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.50/0.64    inference(forward_demodulation,[],[f148,f138])).
% 1.50/0.64  fof(f138,plain,(
% 1.50/0.64    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK2)))),
% 1.50/0.64    inference(resolution,[],[f76,f48])).
% 1.50/0.64  fof(f48,plain,(
% 1.50/0.64    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f76,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.50/0.64    inference(definition_unfolding,[],[f61,f57])).
% 1.50/0.64  fof(f57,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.64    inference(cnf_transformation,[],[f10])).
% 1.50/0.64  fof(f10,axiom,(
% 1.50/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.50/0.64  fof(f61,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f28])).
% 1.50/0.64  fof(f28,plain,(
% 1.50/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/0.64    inference(ennf_transformation,[],[f7])).
% 1.50/0.64  fof(f7,axiom,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.50/0.64  fof(f148,plain,(
% 1.50/0.64    k1_xboole_0 = k5_xboole_0(sK0,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK2))))),
% 1.50/0.64    inference(superposition,[],[f75,f87])).
% 1.50/0.64  fof(f87,plain,(
% 1.50/0.64    k1_relat_1(sK2) = k2_xboole_0(sK0,k1_relat_1(sK2))),
% 1.50/0.64    inference(resolution,[],[f60,f48])).
% 1.50/0.64  fof(f60,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.50/0.64    inference(cnf_transformation,[],[f27])).
% 1.50/0.64  fof(f27,plain,(
% 1.50/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.50/0.64    inference(ennf_transformation,[],[f5])).
% 1.50/0.64  fof(f5,axiom,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.50/0.64  fof(f75,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))))) )),
% 1.50/0.64    inference(definition_unfolding,[],[f56,f73])).
% 1.50/0.64  fof(f73,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.50/0.64    inference(definition_unfolding,[],[f58,f57])).
% 1.50/0.64  fof(f58,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.64    inference(cnf_transformation,[],[f3])).
% 1.50/0.64  fof(f3,axiom,(
% 1.50/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.64  fof(f56,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.64    inference(cnf_transformation,[],[f8])).
% 1.50/0.64  fof(f8,axiom,(
% 1.50/0.64    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.50/0.64  fof(f549,plain,(
% 1.50/0.64    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK1) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(superposition,[],[f78,f520])).
% 1.50/0.64  fof(f520,plain,(
% 1.50/0.64    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(resolution,[],[f519,f102])).
% 1.50/0.64  fof(f102,plain,(
% 1.50/0.64    ( ! [X4,X3] : (~r1_tarski(X3,k1_setfam_1(k2_tarski(X3,X4))) | k1_setfam_1(k2_tarski(X3,X4)) = X3) )),
% 1.50/0.64    inference(resolution,[],[f68,f74])).
% 1.50/0.64  fof(f74,plain,(
% 1.50/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.50/0.64    inference(definition_unfolding,[],[f55,f57])).
% 1.50/0.64  fof(f55,plain,(
% 1.50/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f6])).
% 1.50/0.64  fof(f6,axiom,(
% 1.50/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.50/0.64  fof(f68,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f43])).
% 1.50/0.64  fof(f43,plain,(
% 1.50/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.64    inference(flattening,[],[f42])).
% 1.50/0.64  fof(f42,plain,(
% 1.50/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.64    inference(nnf_transformation,[],[f1])).
% 1.50/0.64  fof(f1,axiom,(
% 1.50/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.64  fof(f519,plain,(
% 1.50/0.64    r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(forward_demodulation,[],[f518,f408])).
% 1.50/0.64  fof(f408,plain,(
% 1.50/0.64    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(superposition,[],[f407,f250])).
% 1.50/0.64  fof(f250,plain,(
% 1.50/0.64    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f249,f45])).
% 1.50/0.64  fof(f45,plain,(
% 1.50/0.64    v1_relat_1(sK2)),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f249,plain,(
% 1.50/0.64    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f248,f46])).
% 1.50/0.64  fof(f46,plain,(
% 1.50/0.64    v1_funct_1(sK2)),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f248,plain,(
% 1.50/0.64    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(resolution,[],[f63,f49])).
% 1.50/0.64  fof(f49,plain,(
% 1.50/0.64    v2_funct_1(sK2)),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f63,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f32])).
% 1.50/0.64  fof(f32,plain,(
% 1.50/0.64    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.64    inference(flattening,[],[f31])).
% 1.50/0.64  fof(f31,plain,(
% 1.50/0.64    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.64    inference(ennf_transformation,[],[f18])).
% 1.50/0.64  fof(f18,axiom,(
% 1.50/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.50/0.64  fof(f407,plain,(
% 1.50/0.64    sK0 = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,sK0)) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(forward_demodulation,[],[f322,f280])).
% 1.50/0.64  fof(f280,plain,(
% 1.50/0.64    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f279,f45])).
% 1.50/0.64  fof(f279,plain,(
% 1.50/0.64    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f278,f46])).
% 1.50/0.64  fof(f278,plain,(
% 1.50/0.64    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(resolution,[],[f64,f49])).
% 1.50/0.64  fof(f64,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f34])).
% 1.50/0.64  fof(f34,plain,(
% 1.50/0.64    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.64    inference(flattening,[],[f33])).
% 1.50/0.64  fof(f33,plain,(
% 1.50/0.64    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.64    inference(ennf_transformation,[],[f17])).
% 1.50/0.64  fof(f17,axiom,(
% 1.50/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.50/0.64  fof(f322,plain,(
% 1.50/0.64    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | (~spl3_5 | ~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(subsumption_resolution,[],[f321,f255])).
% 1.50/0.64  fof(f255,plain,(
% 1.50/0.64    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.50/0.64    inference(avatar_component_clause,[],[f254])).
% 1.50/0.64  fof(f254,plain,(
% 1.50/0.64    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.50/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.50/0.64  fof(f321,plain,(
% 1.50/0.64    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_6 | ~spl3_9)),
% 1.50/0.64    inference(subsumption_resolution,[],[f316,f259])).
% 1.50/0.64  fof(f259,plain,(
% 1.50/0.64    v1_funct_1(k2_funct_1(sK2)) | ~spl3_6),
% 1.50/0.64    inference(avatar_component_clause,[],[f258])).
% 1.50/0.64  fof(f258,plain,(
% 1.50/0.64    spl3_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.50/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.50/0.64  fof(f316,plain,(
% 1.50/0.64    sK0 = k9_relat_1(k2_funct_1(sK2),k10_relat_1(k2_funct_1(sK2),sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_9),
% 1.50/0.64    inference(resolution,[],[f299,f65])).
% 1.50/0.64  fof(f65,plain,(
% 1.50/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f36])).
% 1.50/0.64  fof(f36,plain,(
% 1.50/0.64    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.64    inference(flattening,[],[f35])).
% 1.50/0.64  fof(f35,plain,(
% 1.50/0.64    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.64    inference(ennf_transformation,[],[f15])).
% 1.50/0.64  fof(f15,axiom,(
% 1.50/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.50/0.64  fof(f299,plain,(
% 1.50/0.64    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~spl3_9),
% 1.50/0.64    inference(resolution,[],[f296,f93])).
% 1.50/0.64  fof(f93,plain,(
% 1.50/0.64    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | r1_tarski(sK0,X2)) )),
% 1.50/0.64    inference(superposition,[],[f71,f87])).
% 1.50/0.64  fof(f71,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f37])).
% 1.50/0.64  fof(f37,plain,(
% 1.50/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.50/0.64    inference(ennf_transformation,[],[f4])).
% 1.50/0.64  fof(f4,axiom,(
% 1.50/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.50/0.64  fof(f296,plain,(
% 1.50/0.64    r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl3_9),
% 1.50/0.64    inference(superposition,[],[f271,f94])).
% 1.50/0.64  fof(f94,plain,(
% 1.50/0.64    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 1.50/0.64    inference(resolution,[],[f51,f45])).
% 1.50/0.64  fof(f51,plain,(
% 1.50/0.64    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f23])).
% 1.50/0.64  fof(f23,plain,(
% 1.50/0.64    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.64    inference(ennf_transformation,[],[f12])).
% 1.50/0.64  fof(f12,axiom,(
% 1.50/0.64    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.50/0.64  fof(f271,plain,(
% 1.50/0.64    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))) ) | ~spl3_9),
% 1.50/0.64    inference(avatar_component_clause,[],[f270])).
% 1.50/0.64  fof(f270,plain,(
% 1.50/0.64    spl3_9 <=> ! [X1] : r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2)))),
% 1.50/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.50/0.64  fof(f518,plain,(
% 1.50/0.64    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.50/0.64    inference(subsumption_resolution,[],[f517,f45])).
% 1.50/0.64  fof(f517,plain,(
% 1.50/0.64    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2)),
% 1.50/0.64    inference(subsumption_resolution,[],[f516,f46])).
% 1.50/0.64  fof(f516,plain,(
% 1.50/0.64    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.50/0.64    inference(subsumption_resolution,[],[f512,f49])).
% 1.50/0.64  fof(f512,plain,(
% 1.50/0.64    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.50/0.64    inference(superposition,[],[f62,f463])).
% 1.50/0.64  fof(f463,plain,(
% 1.50/0.64    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.50/0.64    inference(superposition,[],[f334,f136])).
% 1.50/0.64  fof(f136,plain,(
% 1.50/0.64    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.50/0.64    inference(resolution,[],[f76,f47])).
% 1.50/0.64  fof(f47,plain,(
% 1.50/0.64    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.50/0.64    inference(cnf_transformation,[],[f41])).
% 1.50/0.64  fof(f334,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f333,f45])).
% 1.50/0.64  fof(f333,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(subsumption_resolution,[],[f332,f46])).
% 1.50/0.64  fof(f332,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.50/0.64    inference(resolution,[],[f79,f49])).
% 1.50/0.64  fof(f79,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.64    inference(definition_unfolding,[],[f72,f57,f57])).
% 1.50/0.64  fof(f72,plain,(
% 1.50/0.64    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f39])).
% 1.50/0.64  fof(f39,plain,(
% 1.50/0.64    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.50/0.64    inference(flattening,[],[f38])).
% 1.50/0.64  fof(f38,plain,(
% 1.50/0.64    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.50/0.64    inference(ennf_transformation,[],[f14])).
% 1.50/0.64  fof(f14,axiom,(
% 1.50/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 1.50/0.64  fof(f62,plain,(
% 1.50/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f30])).
% 1.50/0.64  fof(f30,plain,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.64    inference(flattening,[],[f29])).
% 1.50/0.64  fof(f29,plain,(
% 1.50/0.64    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.64    inference(ennf_transformation,[],[f16])).
% 1.50/0.64  fof(f16,axiom,(
% 1.50/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.50/0.64  fof(f78,plain,(
% 1.50/0.64    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | r1_tarski(X0,X1)) )),
% 1.50/0.64    inference(definition_unfolding,[],[f69,f73])).
% 1.50/0.64  fof(f69,plain,(
% 1.50/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.50/0.64    inference(cnf_transformation,[],[f44])).
% 1.50/0.64  fof(f44,plain,(
% 1.50/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.50/0.64    inference(nnf_transformation,[],[f2])).
% 1.50/0.64  fof(f2,axiom,(
% 1.50/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.50/0.64  fof(f284,plain,(
% 1.50/0.64    spl3_6),
% 1.50/0.64    inference(avatar_contradiction_clause,[],[f283])).
% 1.50/0.64  fof(f283,plain,(
% 1.50/0.64    $false | spl3_6),
% 1.50/0.64    inference(subsumption_resolution,[],[f282,f45])).
% 1.50/0.64  fof(f282,plain,(
% 1.50/0.64    ~v1_relat_1(sK2) | spl3_6),
% 1.50/0.64    inference(subsumption_resolution,[],[f281,f46])).
% 1.50/0.64  fof(f281,plain,(
% 1.50/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_6),
% 1.50/0.64    inference(resolution,[],[f260,f53])).
% 1.50/0.64  fof(f53,plain,(
% 1.50/0.64    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f25])).
% 1.50/0.64  fof(f25,plain,(
% 1.50/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.64    inference(flattening,[],[f24])).
% 1.50/0.64  fof(f24,plain,(
% 1.50/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.50/0.64    inference(ennf_transformation,[],[f13])).
% 1.50/0.64  fof(f13,axiom,(
% 1.50/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.50/0.64  fof(f260,plain,(
% 1.50/0.64    ~v1_funct_1(k2_funct_1(sK2)) | spl3_6),
% 1.50/0.64    inference(avatar_component_clause,[],[f258])).
% 1.50/0.64  fof(f276,plain,(
% 1.50/0.64    spl3_5),
% 1.50/0.64    inference(avatar_contradiction_clause,[],[f275])).
% 1.50/0.64  fof(f275,plain,(
% 1.50/0.64    $false | spl3_5),
% 1.50/0.64    inference(subsumption_resolution,[],[f274,f45])).
% 1.50/0.64  fof(f274,plain,(
% 1.50/0.64    ~v1_relat_1(sK2) | spl3_5),
% 1.50/0.64    inference(subsumption_resolution,[],[f273,f46])).
% 1.50/0.64  fof(f273,plain,(
% 1.50/0.64    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 1.50/0.64    inference(resolution,[],[f256,f52])).
% 1.50/0.64  fof(f52,plain,(
% 1.50/0.64    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f25])).
% 1.50/0.64  fof(f256,plain,(
% 1.50/0.64    ~v1_relat_1(k2_funct_1(sK2)) | spl3_5),
% 1.50/0.64    inference(avatar_component_clause,[],[f254])).
% 1.50/0.64  fof(f272,plain,(
% 1.50/0.64    ~spl3_5 | spl3_9),
% 1.50/0.64    inference(avatar_split_clause,[],[f252,f270,f254])).
% 1.50/0.64  fof(f252,plain,(
% 1.50/0.64    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,X1),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 1.50/0.64    inference(superposition,[],[f59,f250])).
% 1.50/0.64  fof(f59,plain,(
% 1.50/0.64    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.50/0.64    inference(cnf_transformation,[],[f26])).
% 1.50/0.64  fof(f26,plain,(
% 1.50/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.50/0.64    inference(ennf_transformation,[],[f11])).
% 1.50/0.64  fof(f11,axiom,(
% 1.50/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.50/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.50/0.64  % SZS output end Proof for theBenchmark
% 1.50/0.64  % (24924)------------------------------
% 1.50/0.64  % (24924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.64  % (24924)Termination reason: Refutation
% 1.50/0.64  
% 1.50/0.64  % (24924)Memory used [KB]: 11001
% 1.50/0.64  % (24924)Time elapsed: 0.199 s
% 1.50/0.64  % (24924)------------------------------
% 1.50/0.64  % (24924)------------------------------
% 1.50/0.64  % (24929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.64  % (24917)Success in time 0.275 s
%------------------------------------------------------------------------------
