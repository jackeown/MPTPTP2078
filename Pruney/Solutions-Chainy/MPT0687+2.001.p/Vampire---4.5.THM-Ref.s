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
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 246 expanded)
%              Number of leaves         :   26 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  256 ( 479 expanded)
%              Number of equality atoms :   75 ( 206 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f80,f152,f154,f159,f232,f263,f274,f285,f286])).

fof(f286,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f161,f76,f149,f145])).

fof(f145,plain,
    ( spl3_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f149,plain,
    ( spl3_7
  <=> r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( spl3_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f161,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f160])).

fof(f160,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f48,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f285,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f96,f39])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f96,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_3
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f274,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f122,f98,f95])).

fof(f98,plain,
    ( spl3_4
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f122,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X12,k1_xboole_0)
      | ~ r1_xboole_0(X11,k1_xboole_0) ) ),
    inference(superposition,[],[f91,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f43,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f91,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f263,plain,
    ( ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f247,f99])).

fof(f99,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f247,plain,
    ( ! [X10] : r2_hidden(sK0,X10)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( ! [X10] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(sK0,X10) )
    | ~ spl3_8 ),
    inference(superposition,[],[f215,f231])).

fof(f231,plain,
    ( k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f204,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f204,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 != k4_enumset1(X3,X3,X3,X3,X3,X3) ) ),
    inference(forward_demodulation,[],[f198,f89])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f66,f40])).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f198,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k1_xboole_0)
      | r2_hidden(X3,X4)
      | ~ r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),X4) ) ),
    inference(superposition,[],[f70,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f45,f63])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f232,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f227,f149,f72,f229])).

fof(f72,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f227,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f189,f150])).

fof(f150,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f189,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1) ) ),
    inference(forward_demodulation,[],[f185,f89])).

fof(f185,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k1_xboole_0)
      | ~ r2_hidden(X1,X2)
      | ~ r1_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(superposition,[],[f69,f105])).

fof(f105,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k3_xboole_0(X4,X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f53,f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f45,f63])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f159,plain,
    ( spl3_1
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_1
    | spl3_7 ),
    inference(resolution,[],[f156,f74])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f156,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_7 ),
    inference(resolution,[],[f155,f67])).

fof(f155,plain,
    ( ~ r1_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | spl3_7 ),
    inference(resolution,[],[f151,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f151,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f154,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f153])).

% (16764)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f153,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f147,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f147,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f152,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f143,f76,f149,f145])).

fof(f143,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(superposition,[],[f77,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f80,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f65,f76,f72])).

fof(f65,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f37,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f64,f76,f72])).

fof(f64,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f38,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (16763)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (16754)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (16755)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (16755)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (16758)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (16765)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (16757)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (16762)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f287,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f79,f80,f152,f154,f159,f232,f263,f274,f285,f286])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    ~spl3_6 | spl3_7 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f161,f76,f149,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl3_6 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl3_7 <=> r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_2 <=> k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.47    inference(superposition,[],[f48,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    ~spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    $false | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f96,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl3_3 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    spl3_3 | spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f98,f95])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl3_4 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X12,X11] : (~r2_hidden(X12,k1_xboole_0) | ~r1_xboole_0(X11,k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f91,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(superposition,[],[f43,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(superposition,[],[f47,f43])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    ~spl3_4 | ~spl3_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    $false | (~spl3_4 | ~spl3_8)),
% 0.21/0.47    inference(resolution,[],[f247,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    ( ! [X10] : (r2_hidden(sK0,X10)) ) | ~spl3_8),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f246])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    ( ! [X10] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,X10)) ) | ~spl3_8),
% 0.21/0.47    inference(superposition,[],[f215,f231])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f229])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    spl3_8 <=> k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f212])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f204,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f50,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f44,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f57,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f58,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    ( ! [X4,X3] : (~r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),X4) | r2_hidden(X3,X4) | k1_xboole_0 != k4_enumset1(X3,X3,X3,X3,X3,X3)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f198,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(forward_demodulation,[],[f66,f40])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f41,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k1_xboole_0 != k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k1_xboole_0) | r2_hidden(X3,X4) | ~r1_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),X4)) )),
% 0.21/0.47    inference(superposition,[],[f70,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f55,f45,f63])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f227,f149,f72,f229])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl3_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k2_relat_1(sK1)) | k1_xboole_0 = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f189,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~r1_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)) | ~r2_hidden(X1,X2) | k1_xboole_0 = k4_enumset1(X1,X1,X1,X1,X1,X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f185,f89])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k1_xboole_0) | ~r2_hidden(X1,X2) | ~r1_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.21/0.47    inference(superposition,[],[f69,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) )),
% 0.21/0.47    inference(superposition,[],[f53,f43])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f56,f45,f63])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl3_1 | spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    $false | (spl3_1 | spl3_7)),
% 0.21/0.47    inference(resolution,[],[f156,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_relat_1(sK1)) | spl3_7),
% 0.21/0.47    inference(resolution,[],[f155,f67])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~r1_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) | spl3_7),
% 0.21/0.47    inference(resolution,[],[f151,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.47  % (16764)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    $false | spl3_6),
% 0.21/0.47    inference(resolution,[],[f147,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f18])).
% 0.21/0.47  fof(f18,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f145])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ~spl3_6 | ~spl3_7 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f143,f76,f149,f145])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl3_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK1) | spl3_2),
% 0.21/0.47    inference(superposition,[],[f77,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f76,f72])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f37,f63])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f76,f72])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k1_xboole_0 = k10_relat_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f38,f63])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16755)------------------------------
% 0.21/0.47  % (16755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16755)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16755)Memory used [KB]: 6140
% 0.21/0.47  % (16755)Time elapsed: 0.057 s
% 0.21/0.47  % (16755)------------------------------
% 0.21/0.47  % (16755)------------------------------
% 0.21/0.47  % (16750)Success in time 0.114 s
%------------------------------------------------------------------------------
