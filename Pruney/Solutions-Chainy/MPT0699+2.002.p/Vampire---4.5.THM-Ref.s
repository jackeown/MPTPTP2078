%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 159 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  250 ( 467 expanded)
%              Number of equality atoms :   68 ( 120 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f80,f82,f91,f93,f183,f1077,f1126])).

fof(f1126,plain,(
    ~ spl2_81 ),
    inference(avatar_contradiction_clause,[],[f1090])).

fof(f1090,plain,
    ( $false
    | ~ spl2_81 ),
    inference(subsumption_resolution,[],[f36,f1076])).

fof(f1076,plain,
    ( ! [X7] : k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7)
    | ~ spl2_81 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f1075,plain,
    ( spl2_81
  <=> ! [X7] : k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).

fof(f36,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f1077,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_81
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f1073,f180,f89,f85,f1075,f70,f66])).

fof(f66,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f70,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_4
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( spl2_5
  <=> ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f180,plain,
    ( spl2_12
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f1073,plain,
    ( ! [X7] :
        ( k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f1072,f108])).

fof(f108,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k3_xboole_0(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f105,f61])).

fof(f61,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f50,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f105,plain,(
    ! [X5] : k9_relat_1(sK1,X5) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X5)) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f1072,plain,
    ( ! [X7] :
        ( k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,k3_xboole_0(X7,k1_relat_1(sK1)))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f1042,f749])).

fof(f749,plain,
    ( ! [X2] : k3_xboole_0(X2,k1_relat_1(sK1)) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f748,f262])).

fof(f262,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k10_relat_1(k6_relat_1(X3),X4) ),
    inference(forward_demodulation,[],[f261,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f261,plain,(
    ! [X4,X3] : k10_relat_1(k6_relat_1(X3),X4) = k1_relat_1(k6_relat_1(k3_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f259,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f259,plain,(
    ! [X4,X3] : k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k10_relat_1(k6_relat_1(X3),X4) ),
    inference(resolution,[],[f130,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f130,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,X4) ) ),
    inference(forward_demodulation,[],[f122,f39])).

fof(f122,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,k1_relat_1(k6_relat_1(X4))) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f748,plain,
    ( ! [X2] : k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X2)
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f742,f182])).

fof(f182,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f742,plain,
    ( ! [X2] : k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X2) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2))
    | ~ spl2_4 ),
    inference(resolution,[],[f681,f86])).

fof(f86,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f681,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k10_relat_1(k5_relat_1(sK1,X14),X15) = k10_relat_1(sK1,k10_relat_1(X14,X15)) ) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f1042,plain,
    ( ! [X7] :
        ( k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X7)))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_5 ),
    inference(resolution,[],[f55,f90])).

fof(f90,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f183,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_12 ),
    inference(avatar_split_clause,[],[f177,f180,f70,f66])).

fof(f177,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f93,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f92,f85,f70,f66])).

fof(f92,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_4 ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f87,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f91,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f83,f74,f89,f85])).

fof(f74,plain,
    ( spl2_3
  <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl2_3 ),
    inference(superposition,[],[f52,f76])).

fof(f76,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f82,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f34,f72])).

fof(f72,plain,
    ( ~ v1_funct_1(sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f33,f68])).

fof(f68,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f77,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f63,f74,f70,f66])).

fof(f63,plain,
    ( k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (15138)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (15148)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (15139)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (15133)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (15140)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (15147)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (15149)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (15137)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (15145)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (15142)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (15136)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (15135)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (15146)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (15134)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (15143)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (15141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (15144)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (15149)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1135,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f77,f80,f82,f91,f93,f183,f1077,f1126])).
% 0.21/0.51  fof(f1126,plain,(
% 0.21/0.51    ~spl2_81),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1090])).
% 0.21/0.51  fof(f1090,plain,(
% 0.21/0.51    $false | ~spl2_81),
% 0.21/0.51    inference(subsumption_resolution,[],[f36,f1076])).
% 0.21/0.51  fof(f1076,plain,(
% 0.21/0.51    ( ! [X7] : (k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7)) ) | ~spl2_81),
% 0.21/0.51    inference(avatar_component_clause,[],[f1075])).
% 0.21/0.51  fof(f1075,plain,(
% 0.21/0.51    spl2_81 <=> ! [X7] : k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_81])])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1] : ((k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.51  fof(f1077,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_81 | ~spl2_4 | ~spl2_5 | ~spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f1073,f180,f89,f85,f1075,f70,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_4 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl2_5 <=> ! [X0] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl2_12 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.51  fof(f1073,plain,(
% 0.21/0.51    ( ! [X7] : (k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,X7) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_4 | ~spl2_5 | ~spl2_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f1072,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k3_xboole_0(X0,k1_relat_1(sK1)))) )),
% 0.21/0.51    inference(superposition,[],[f105,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.51    inference(superposition,[],[f56,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f50,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X5] : (k9_relat_1(sK1,X5) = k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X5))) )),
% 0.21/0.51    inference(resolution,[],[f53,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.51  fof(f1072,plain,(
% 0.21/0.51    ( ! [X7] : (k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,k3_xboole_0(X7,k1_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl2_4 | ~spl2_5 | ~spl2_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f1042,f749])).
% 0.21/0.51  fof(f749,plain,(
% 0.21/0.51    ( ! [X2] : (k3_xboole_0(X2,k1_relat_1(sK1)) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2))) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f748,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k10_relat_1(k6_relat_1(X3),X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f261,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k10_relat_1(k6_relat_1(X3),X4) = k1_relat_1(k6_relat_1(k3_xboole_0(X4,X3)))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f259,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k10_relat_1(k6_relat_1(X3),X4)) )),
% 0.21/0.51    inference(resolution,[],[f130,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f122,f39])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~v1_relat_1(X3) | k1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) = k10_relat_1(X3,k1_relat_1(k6_relat_1(X4)))) )),
% 0.21/0.51    inference(resolution,[],[f41,f37])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.51  fof(f748,plain,(
% 0.21/0.51    ( ! [X2] : (k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X2)) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f742,f182])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~spl2_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f742,plain,(
% 0.21/0.51    ( ! [X2] : (k10_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)),X2) = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X2))) ) | ~spl2_4),
% 0.21/0.51    inference(resolution,[],[f681,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK1)) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f681,plain,(
% 0.21/0.51    ( ! [X14,X15] : (~v1_relat_1(X14) | k10_relat_1(k5_relat_1(sK1,X14),X15) = k10_relat_1(sK1,k10_relat_1(X14,X15))) )),
% 0.21/0.51    inference(resolution,[],[f54,f33])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 0.21/0.51  fof(f1042,plain,(
% 0.21/0.51    ( ! [X7] : (k10_relat_1(k2_funct_1(sK1),X7) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),X7))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_5),
% 0.21/0.51    inference(resolution,[],[f55,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1))) ) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f180,f70,f66])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f46,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f92,f85,f70,f66])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_4),
% 0.21/0.51    inference(resolution,[],[f87,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK1)) | spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~spl2_4 | spl2_5 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f83,f74,f89,f85])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl2_3 <=> k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X0),k2_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl2_3),
% 0.21/0.51    inference(superposition,[],[f52,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    $false | spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f34,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    $false | spl2_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f33,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f74,f70,f66])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f44,f35])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (15149)------------------------------
% 0.21/0.51  % (15149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15149)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (15149)Memory used [KB]: 7036
% 0.21/0.51  % (15149)Time elapsed: 0.072 s
% 0.21/0.51  % (15149)------------------------------
% 0.21/0.51  % (15149)------------------------------
% 0.21/0.51  % (15132)Success in time 0.15 s
%------------------------------------------------------------------------------
