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
% DateTime   : Thu Dec  3 12:51:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 131 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 257 expanded)
%              Number of equality atoms :   51 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f116,f137,f151,f292])).

fof(f292,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f248,f36])).

fof(f36,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f248,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_10 ),
    inference(resolution,[],[f240,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f240,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_10 ),
    inference(resolution,[],[f202,f150])).

fof(f150,plain,
    ( ~ r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_10
  <=> r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(forward_demodulation,[],[f195,f152])).

fof(f152,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f62,f139])).

fof(f139,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f61,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f60])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(superposition,[],[f42,f135])).

fof(f135,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f126,f38])).

fof(f126,plain,(
    ! [X4,X2,X3] :
      ( k3_xboole_0(X2,k3_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X2,X4),k1_xboole_0)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f53,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f151,plain,
    ( ~ spl5_3
    | ~ spl5_10
    | spl5_7 ),
    inference(avatar_split_clause,[],[f146,f103,f148,f86])).

fof(f86,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( spl5_7
  <=> r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f146,plain,
    ( ~ r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0))
    | ~ v1_relat_1(sK2)
    | spl5_7 ),
    inference(superposition,[],[f105,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f105,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f137,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f120,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(resolution,[],[f101,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_6
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f88,f35])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f106,plain,
    ( ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f84,f103,f99])).

fof(f84,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f37,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (848)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (857)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (853)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (847)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (851)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (863)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (854)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (856)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (860)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (851)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f106,f116,f137,f151,f292])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    spl5_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    $false | spl5_10),
% 0.21/0.53    inference(resolution,[],[f248,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r1_xboole_0(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f18])).
% 0.21/0.53  fof(f18,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ~r1_xboole_0(sK0,sK1) | spl5_10),
% 0.21/0.53    inference(resolution,[],[f240,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,sK0) | spl5_10),
% 0.21/0.53    inference(resolution,[],[f202,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0)) | spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl5_10 <=> r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f195,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(superposition,[],[f62,f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k1_xboole_0) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f61,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f46,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f43,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f44,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f54,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f45,f59])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2)) )),
% 0.21/0.53    inference(superposition,[],[f42,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f126,f38])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X2,X4),k1_xboole_0) | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.53    inference(superposition,[],[f53,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f48,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~spl5_3 | ~spl5_10 | spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f146,f103,f148,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl5_3 <=> v1_relat_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl5_7 <=> r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,k3_xboole_0(k1_relat_1(sK2),sK0)) | ~v1_relat_1(sK2) | spl5_7),
% 0.21/0.53    inference(superposition,[],[f105,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0))) | spl5_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f103])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    $false | spl5_6),
% 0.21/0.53    inference(resolution,[],[f120,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | spl5_6),
% 0.21/0.53    inference(resolution,[],[f101,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl5_6 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    $false | spl5_3),
% 0.21/0.53    inference(resolution,[],[f88,f35])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ~spl5_6 | ~spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f84,f103,f99])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,k1_relat_1(k7_relat_1(sK2,sK0))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.53    inference(superposition,[],[f37,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (851)------------------------------
% 0.21/0.53  % (851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (851)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (851)Memory used [KB]: 6268
% 0.21/0.53  % (851)Time elapsed: 0.087 s
% 0.21/0.53  % (851)------------------------------
% 0.21/0.53  % (851)------------------------------
% 0.21/0.53  % (845)Success in time 0.17 s
%------------------------------------------------------------------------------
