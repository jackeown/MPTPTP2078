%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 533 expanded)
%              Number of leaves         :   24 ( 179 expanded)
%              Depth                    :   17
%              Number of atoms          :  240 ( 808 expanded)
%              Number of equality atoms :   48 ( 462 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f105,f107,f122,f178,f180,f216,f366,f368,f370])).

fof(f370,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f359,f34])).

fof(f34,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f359,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl3_10
  <=> v1_funct_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f368,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f355,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f355,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl3_9
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f366,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_4 ),
    inference(avatar_split_clause,[],[f365,f115,f357,f353])).

fof(f115,plain,
    ( spl3_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f365,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f351,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f351,plain,
    ( r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f301,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(f301,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2))))) ),
    inference(backward_demodulation,[],[f161,f244])).

fof(f244,plain,(
    ! [X2,X3] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)) ),
    inference(superposition,[],[f231,f159])).

fof(f159,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ),
    inference(backward_demodulation,[],[f123,f131])).

fof(f131,plain,(
    ! [X4,X5] : k2_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) = k1_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) ),
    inference(superposition,[],[f35,f123])).

fof(f123,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ),
    inference(backward_demodulation,[],[f59,f66])).

fof(f66,plain,(
    ! [X8,X9] : k1_setfam_1(k5_enumset1(X8,X8,X8,X8,X8,X8,X9)) = k2_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X8))) ),
    inference(superposition,[],[f36,f59])).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f231,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(forward_demodulation,[],[f75,f67])).

fof(f67,plain,(
    ! [X10,X11] : k1_setfam_1(k5_enumset1(X10,X10,X10,X10,X10,X10,X11)) = k1_relat_1(k5_relat_1(k6_relat_1(X11),k6_relat_1(X10))) ),
    inference(superposition,[],[f35,f59])).

fof(f75,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f55,f55])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f161,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f124,f131])).

fof(f124,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f74,f66])).

fof(f74,plain,(
    r2_hidden(sK0,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f57,plain,(
    r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1))) ),
    inference(definition_unfolding,[],[f31,f56])).

fof(f31,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f216,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f171,f34])).

fof(f171,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_7
  <=> v1_funct_1(k6_relat_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f180,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f167,f33])).

fof(f167,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK2)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_6
  <=> v1_relat_1(k6_relat_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f178,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f177,f119,f169,f165])).

fof(f119,plain,
    ( spl3_5
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f177,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f163,f35])).

fof(f163,plain,
    ( r2_hidden(sK0,k1_relat_1(k6_relat_1(k1_relat_1(sK2))))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK2))) ),
    inference(resolution,[],[f161,f46])).

fof(f122,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f113,f100,f119,f115,f92])).

fof(f92,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f102,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f107,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f98,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f94,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f103,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f90,f100,f96,f92])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f32,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (18252)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (18255)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (18259)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (18256)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (18254)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (18255)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f371,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f103,f105,f107,f122,f178,f180,f216,f366,f368,f370])).
% 0.22/0.48  fof(f370,plain,(
% 0.22/0.48    spl3_10),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f369])).
% 0.22/0.48  fof(f369,plain,(
% 0.22/0.48    $false | spl3_10),
% 0.22/0.48    inference(resolution,[],[f359,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.48  fof(f359,plain,(
% 0.22/0.48    ~v1_funct_1(k6_relat_1(sK1)) | spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f357])).
% 0.22/0.48  fof(f357,plain,(
% 0.22/0.48    spl3_10 <=> v1_funct_1(k6_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f368,plain,(
% 0.22/0.48    spl3_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f367])).
% 0.22/0.48  fof(f367,plain,(
% 0.22/0.48    $false | spl3_9),
% 0.22/0.48    inference(resolution,[],[f355,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f355,plain,(
% 0.22/0.48    ~v1_relat_1(k6_relat_1(sK1)) | spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f353])).
% 0.22/0.48  fof(f353,plain,(
% 0.22/0.48    spl3_9 <=> v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f366,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_10 | spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f365,f115,f357,f353])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl3_4 <=> r2_hidden(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f365,plain,(
% 0.22/0.48    r2_hidden(sK0,sK1) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f351,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.48  fof(f351,plain,(
% 0.22/0.48    r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.22/0.48    inference(resolution,[],[f301,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).
% 0.22/0.48  fof(f301,plain,(
% 0.22/0.48    r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(k1_relat_1(sK2)))))),
% 0.22/0.48    inference(backward_demodulation,[],[f161,f244])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) )),
% 0.22/0.48    inference(superposition,[],[f231,f159])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f123,f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ( ! [X4,X5] : (k2_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) = k1_relat_1(k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)))) )),
% 0.22/0.48    inference(superposition,[],[f35,f123])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f59,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X8,X9] : (k1_setfam_1(k5_enumset1(X8,X8,X8,X8,X8,X8,X9)) = k2_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X8)))) )),
% 0.22/0.48    inference(superposition,[],[f36,f59])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f40,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f38,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f41,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f49,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f50,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.48  fof(f231,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f75,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X10,X11] : (k1_setfam_1(k5_enumset1(X10,X10,X10,X10,X10,X10,X11)) = k1_relat_1(k5_relat_1(k6_relat_1(X11),k6_relat_1(X10)))) )),
% 0.22/0.48    inference(superposition,[],[f35,f59])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) )),
% 0.22/0.48    inference(superposition,[],[f59,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f55,f55])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))))),
% 0.22/0.49    inference(backward_demodulation,[],[f124,f131])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    r2_hidden(sK0,k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k6_relat_1(sK1))))),
% 0.22/0.49    inference(backward_demodulation,[],[f74,f66])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_setfam_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k1_relat_1(sK2))))),
% 0.22/0.49    inference(backward_demodulation,[],[f57,f58])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_setfam_1(k5_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),sK1)))),
% 0.22/0.49    inference(definition_unfolding,[],[f31,f56])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f14])).
% 0.22/0.49  fof(f14,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    $false | spl3_7),
% 0.22/0.49    inference(resolution,[],[f171,f34])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ~v1_funct_1(k6_relat_1(k1_relat_1(sK2))) | spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f169])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    spl3_7 <=> v1_funct_1(k6_relat_1(k1_relat_1(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f179])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    $false | spl3_6),
% 0.22/0.49    inference(resolution,[],[f167,f33])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ~v1_relat_1(k6_relat_1(k1_relat_1(sK2))) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f165])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl3_6 <=> v1_relat_1(k6_relat_1(k1_relat_1(sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~spl3_6 | ~spl3_7 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f177,f119,f169,f165])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl3_5 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k6_relat_1(k1_relat_1(sK2))) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK2)))),
% 0.22/0.49    inference(forward_demodulation,[],[f163,f35])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(k6_relat_1(k1_relat_1(sK2)))) | ~v1_funct_1(k6_relat_1(k1_relat_1(sK2))) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK2)))),
% 0.22/0.49    inference(resolution,[],[f161,f46])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_4 | ~spl3_5 | spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f113,f100,f119,f115,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl3_3 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,sK1) | ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(resolution,[],[f102,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    $false | spl3_2),
% 0.22/0.49    inference(resolution,[],[f98,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    $false | spl3_1),
% 0.22/0.49    inference(resolution,[],[f94,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f100,f96,f92])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(superposition,[],[f32,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18255)------------------------------
% 0.22/0.49  % (18255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18255)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18255)Memory used [KB]: 6396
% 0.22/0.49  % (18255)Time elapsed: 0.065 s
% 0.22/0.49  % (18255)------------------------------
% 0.22/0.49  % (18255)------------------------------
% 0.22/0.49  % (18260)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (18250)Success in time 0.123 s
%------------------------------------------------------------------------------
