%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 160 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  239 ( 514 expanded)
%              Number of equality atoms :   50 ( 149 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f89,f102,f122,f130,f138])).

fof(f138,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f132,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f132,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(sK2(sK0,k2_relat_1(sK1),sK1),sK2(sK0,k2_relat_1(sK1),sK1),X0),k1_xboole_0)
    | ~ spl3_6 ),
    inference(resolution,[],[f129,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f129,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_6
  <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f130,plain,
    ( ~ spl3_1
    | spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f125,f120,f62,f127,f58])).

fof(f58,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f62,plain,
    ( spl3_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f120,plain,
    ( spl3_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f125,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(superposition,[],[f121,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f121,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f117,f120,f94])).

fof(f94,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f116,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(X0,k2_relat_1(sK1),sK1)),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f115,f67])).

fof(f67,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK1)),sK1) ) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f102,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f96,f33])).

fof(f96,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f89,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | spl3_2 ),
    inference(superposition,[],[f64,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | spl3_1 ),
    inference(superposition,[],[f83,f70])).

fof(f70,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f83,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_1 ),
    inference(forward_demodulation,[],[f82,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f82,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_1 ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_1 ),
    inference(resolution,[],[f72,f59])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f72,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,sK0)) )
    | spl3_1 ),
    inference(resolution,[],[f71,f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X1,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X1,X1,X0)) ) ),
    inference(resolution,[],[f55,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f64,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f66,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62,f58])).

fof(f35,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f62,f58])).

fof(f34,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (17601)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (17601)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f65,f66,f89,f102,f122,f130,f138])).
% 0.21/0.45  fof(f138,plain,(
% 0.21/0.45    ~spl3_6),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.45  fof(f137,plain,(
% 0.21/0.45    $false | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f132,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.45  fof(f132,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK2(sK0,k2_relat_1(sK1),sK1),sK2(sK0,k2_relat_1(sK1),sK1),X0),k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.45    inference(resolution,[],[f129,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f52,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.21/0.45  fof(f129,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f127])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    spl3_6 <=> r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ~spl3_1 | spl3_6 | ~spl3_2 | ~spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f125,f120,f62,f127,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl3_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    spl3_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    spl3_5 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    r2_hidden(sK2(sK0,k2_relat_1(sK1),sK1),k1_xboole_0) | ~r2_hidden(sK0,k1_relat_1(sK1)) | (~spl3_2 | ~spl3_5)),
% 0.21/0.45    inference(superposition,[],[f121,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f120])).
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    ~spl3_3 | spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f117,f120,f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl3_3 <=> v1_relat_1(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(sK2(X0,k2_relat_1(sK1),sK1),k11_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.45    inference(resolution,[],[f116,f49])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(nnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(X0,k2_relat_1(sK1),sK1)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.45    inference(superposition,[],[f115,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.45    inference(resolution,[],[f40,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.45    inference(negated_conjecture,[],[f13])).
% 0.21/0.45  fof(f13,conjecture,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK1)),sK1)) )),
% 0.21/0.45    inference(resolution,[],[f46,f33])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(rectify,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(nnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    $false | spl3_3),
% 0.21/0.45    inference(resolution,[],[f96,f33])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl3_1 | spl3_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    $false | (spl3_1 | spl3_2)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | (spl3_1 | spl3_2)),
% 0.21/0.45    inference(superposition,[],[f64,f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    k1_xboole_0 = k11_relat_1(sK1,sK0) | spl3_1),
% 0.21/0.45    inference(superposition,[],[f83,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.45    inference(resolution,[],[f54,f33])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f41,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f39,f43])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_1),
% 0.21/0.45    inference(forward_demodulation,[],[f82,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_1),
% 0.21/0.45    inference(superposition,[],[f68,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_1),
% 0.21/0.45    inference(resolution,[],[f72,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,sK0))) ) | spl3_1),
% 0.21/0.45    inference(resolution,[],[f71,f59])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X1,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X1,X1,X0))) )),
% 0.21/0.45    inference(resolution,[],[f55,f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,X0)) )),
% 0.21/0.45    inference(resolution,[],[f42,f33])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f51,f43])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.21/0.45    inference(resolution,[],[f44,f33])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f62])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ~spl3_1 | spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f35,f62,f58])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_1 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f34,f62,f58])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (17601)------------------------------
% 0.21/0.45  % (17601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (17601)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (17601)Memory used [KB]: 6140
% 0.21/0.45  % (17601)Time elapsed: 0.039 s
% 0.21/0.45  % (17601)------------------------------
% 0.21/0.45  % (17601)------------------------------
% 0.21/0.45  % (17598)Success in time 0.092 s
%------------------------------------------------------------------------------
