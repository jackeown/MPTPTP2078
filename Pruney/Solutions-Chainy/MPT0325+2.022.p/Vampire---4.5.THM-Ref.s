%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:41 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 165 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  207 ( 378 expanded)
%              Number of equality atoms :   75 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f56,f132,f440,f597,f890,f973,f7609,f7656,f7660,f7746,f7790,f7877])).

fof(f7877,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_285 ),
    inference(avatar_split_clause,[],[f7874,f7658,f32,f395])).

fof(f395,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f7658,plain,
    ( spl4_285
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_285])])).

fof(f7874,plain,
    ( k1_xboole_0 = sK1
    | spl4_1
    | ~ spl4_285 ),
    inference(resolution,[],[f7659,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X0))
        | k1_xboole_0 = X0 )
    | spl4_1 ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f7659,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_285 ),
    inference(avatar_component_clause,[],[f7658])).

fof(f7790,plain,
    ( spl4_2
    | ~ spl4_306 ),
    inference(avatar_split_clause,[],[f7750,f7744,f35])).

fof(f35,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f7744,plain,
    ( spl4_306
  <=> sK1 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f7750,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_306 ),
    inference(superposition,[],[f46,f7745])).

fof(f7745,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_306 ),
    inference(avatar_component_clause,[],[f7744])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f7746,plain,
    ( spl4_306
    | spl4_41
    | ~ spl4_284 ),
    inference(avatar_split_clause,[],[f7741,f7654,f785,f7744])).

fof(f785,plain,
    ( spl4_41
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f7654,plain,
    ( spl4_284
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).

fof(f7741,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k3_xboole_0(sK1,sK3)
    | ~ spl4_284 ),
    inference(resolution,[],[f7655,f172])).

fof(f172,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
      | k1_xboole_0 = X1
      | k3_xboole_0(X2,X3) = X2 ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7655,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_284 ),
    inference(avatar_component_clause,[],[f7654])).

fof(f7660,plain,
    ( spl4_285
    | ~ spl4_283 ),
    inference(avatar_split_clause,[],[f7614,f7502,f7658])).

fof(f7502,plain,
    ( spl4_283
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_283])])).

fof(f7614,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_283 ),
    inference(superposition,[],[f46,f7503])).

fof(f7503,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_283 ),
    inference(avatar_component_clause,[],[f7502])).

fof(f7656,plain,
    ( spl4_284
    | ~ spl4_283 ),
    inference(avatar_split_clause,[],[f7611,f7502,f7654])).

fof(f7611,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))
    | ~ spl4_283 ),
    inference(superposition,[],[f20,f7503])).

fof(f7609,plain,
    ( spl4_283
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f7358,f130,f7502])).

fof(f130,plain,
    ( spl4_8
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f7358,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1))
    | ~ spl4_8 ),
    inference(superposition,[],[f131,f1229])).

fof(f1229,plain,(
    ! [X6,X4,X7,X5] : k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)) = k3_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X4,X7)) ),
    inference(superposition,[],[f245,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f245,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X1,X0),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f21])).

fof(f131,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f973,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | spl4_55 ),
    inference(trivial_inequality_removal,[],[f971])).

fof(f971,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_55 ),
    inference(superposition,[],[f889,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f889,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f888])).

fof(f888,plain,
    ( spl4_55
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f890,plain,
    ( ~ spl4_55
    | spl4_3
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f854,f785,f39,f888])).

fof(f39,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f854,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl4_3
    | ~ spl4_41 ),
    inference(superposition,[],[f40,f786])).

fof(f786,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f785])).

fof(f40,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f597,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | spl4_21 ),
    inference(trivial_inequality_removal,[],[f595])).

fof(f595,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_21 ),
    inference(superposition,[],[f439,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f439,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl4_21
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f440,plain,
    ( ~ spl4_21
    | spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f425,f395,f39,f438])).

fof(f425,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f40,f396])).

fof(f396,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f395])).

fof(f132,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f119,f54,f130])).

fof(f54,plain,
    ( spl4_5
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f119,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(superposition,[],[f95,f55])).

fof(f55,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f95,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f52,f21])).

fof(f52,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f22,f46])).

fof(f56,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f50,f43,f54])).

fof(f43,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f50,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f22,f44])).

fof(f44,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k2_zfmisc_1(X0,X1) != k1_xboole_0
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f41,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f35,f32])).

fof(f19,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (4348)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (4341)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (4355)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (4352)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (4345)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (4351)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (4347)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (4342)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4357)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (4356)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (4350)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (4346)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (4343)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (4353)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4360)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (4361)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (4361)Refutation not found, incomplete strategy% (4361)------------------------------
% 0.21/0.51  % (4361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4361)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4361)Memory used [KB]: 10490
% 0.21/0.51  % (4361)Time elapsed: 0.095 s
% 0.21/0.51  % (4361)------------------------------
% 0.21/0.51  % (4361)------------------------------
% 0.21/0.51  % (4344)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (4342)Refutation not found, incomplete strategy% (4342)------------------------------
% 0.21/0.52  % (4342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4342)Memory used [KB]: 10618
% 0.21/0.52  % (4342)Time elapsed: 0.101 s
% 0.21/0.52  % (4342)------------------------------
% 0.21/0.52  % (4342)------------------------------
% 0.21/0.52  % (4349)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (4354)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (4358)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (4359)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 3.50/0.84  % (4347)Refutation found. Thanks to Tanya!
% 3.50/0.84  % SZS status Theorem for theBenchmark
% 3.50/0.84  % SZS output start Proof for theBenchmark
% 3.50/0.84  fof(f7882,plain,(
% 3.50/0.84    $false),
% 3.50/0.84    inference(avatar_sat_refutation,[],[f37,f41,f45,f56,f132,f440,f597,f890,f973,f7609,f7656,f7660,f7746,f7790,f7877])).
% 3.50/0.84  fof(f7877,plain,(
% 3.50/0.84    spl4_13 | spl4_1 | ~spl4_285),
% 3.50/0.84    inference(avatar_split_clause,[],[f7874,f7658,f32,f395])).
% 3.50/0.84  fof(f395,plain,(
% 3.50/0.84    spl4_13 <=> k1_xboole_0 = sK1),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.50/0.84  fof(f32,plain,(
% 3.50/0.84    spl4_1 <=> r1_tarski(sK0,sK2)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.50/0.84  fof(f7658,plain,(
% 3.50/0.84    spl4_285 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_285])])).
% 3.50/0.84  fof(f7874,plain,(
% 3.50/0.84    k1_xboole_0 = sK1 | (spl4_1 | ~spl4_285)),
% 3.50/0.84    inference(resolution,[],[f7659,f161])).
% 3.50/0.84  fof(f161,plain,(
% 3.50/0.84    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK2,X0)) | k1_xboole_0 = X0) ) | spl4_1),
% 3.50/0.84    inference(resolution,[],[f26,f33])).
% 3.50/0.84  fof(f33,plain,(
% 3.50/0.84    ~r1_tarski(sK0,sK2) | spl4_1),
% 3.50/0.84    inference(avatar_component_clause,[],[f32])).
% 3.50/0.84  fof(f26,plain,(
% 3.50/0.84    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 3.50/0.84    inference(cnf_transformation,[],[f12])).
% 3.50/0.84  fof(f12,plain,(
% 3.50/0.84    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 3.50/0.84    inference(ennf_transformation,[],[f5])).
% 3.50/0.84  fof(f5,axiom,(
% 3.50/0.84    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 3.50/0.84  fof(f7659,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl4_285),
% 3.50/0.84    inference(avatar_component_clause,[],[f7658])).
% 3.50/0.84  fof(f7790,plain,(
% 3.50/0.84    spl4_2 | ~spl4_306),
% 3.50/0.84    inference(avatar_split_clause,[],[f7750,f7744,f35])).
% 3.50/0.84  fof(f35,plain,(
% 3.50/0.84    spl4_2 <=> r1_tarski(sK1,sK3)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.50/0.84  fof(f7744,plain,(
% 3.50/0.84    spl4_306 <=> sK1 = k3_xboole_0(sK1,sK3)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).
% 3.50/0.84  fof(f7750,plain,(
% 3.50/0.84    r1_tarski(sK1,sK3) | ~spl4_306),
% 3.50/0.84    inference(superposition,[],[f46,f7745])).
% 3.50/0.84  fof(f7745,plain,(
% 3.50/0.84    sK1 = k3_xboole_0(sK1,sK3) | ~spl4_306),
% 3.50/0.84    inference(avatar_component_clause,[],[f7744])).
% 3.50/0.84  fof(f46,plain,(
% 3.50/0.84    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.50/0.84    inference(superposition,[],[f20,f21])).
% 3.50/0.84  fof(f21,plain,(
% 3.50/0.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.50/0.84    inference(cnf_transformation,[],[f1])).
% 3.50/0.84  fof(f1,axiom,(
% 3.50/0.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.50/0.84  fof(f20,plain,(
% 3.50/0.84    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.50/0.84    inference(cnf_transformation,[],[f2])).
% 3.50/0.84  fof(f2,axiom,(
% 3.50/0.84    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.50/0.84  fof(f7746,plain,(
% 3.50/0.84    spl4_306 | spl4_41 | ~spl4_284),
% 3.50/0.84    inference(avatar_split_clause,[],[f7741,f7654,f785,f7744])).
% 3.50/0.84  fof(f785,plain,(
% 3.50/0.84    spl4_41 <=> k1_xboole_0 = sK0),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 3.50/0.84  fof(f7654,plain,(
% 3.50/0.84    spl4_284 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_284])])).
% 3.50/0.84  fof(f7741,plain,(
% 3.50/0.84    k1_xboole_0 = sK0 | sK1 = k3_xboole_0(sK1,sK3) | ~spl4_284),
% 3.50/0.84    inference(resolution,[],[f7655,f172])).
% 3.50/0.84  fof(f172,plain,(
% 3.50/0.84    ( ! [X2,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) | k1_xboole_0 = X1 | k3_xboole_0(X2,X3) = X2) )),
% 3.50/0.84    inference(resolution,[],[f27,f22])).
% 3.50/0.84  fof(f22,plain,(
% 3.50/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.50/0.84    inference(cnf_transformation,[],[f11])).
% 3.50/0.84  fof(f11,plain,(
% 3.50/0.84    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.50/0.84    inference(ennf_transformation,[],[f3])).
% 3.50/0.84  fof(f3,axiom,(
% 3.50/0.84    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.50/0.84  fof(f27,plain,(
% 3.50/0.84    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 3.50/0.84    inference(cnf_transformation,[],[f12])).
% 3.50/0.84  fof(f7655,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl4_284),
% 3.50/0.84    inference(avatar_component_clause,[],[f7654])).
% 3.50/0.84  fof(f7660,plain,(
% 3.50/0.84    spl4_285 | ~spl4_283),
% 3.50/0.84    inference(avatar_split_clause,[],[f7614,f7502,f7658])).
% 3.50/0.84  fof(f7502,plain,(
% 3.50/0.84    spl4_283 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_283])])).
% 3.50/0.84  fof(f7614,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) | ~spl4_283),
% 3.50/0.84    inference(superposition,[],[f46,f7503])).
% 3.50/0.84  fof(f7503,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1)) | ~spl4_283),
% 3.50/0.84    inference(avatar_component_clause,[],[f7502])).
% 3.50/0.84  fof(f7656,plain,(
% 3.50/0.84    spl4_284 | ~spl4_283),
% 3.50/0.84    inference(avatar_split_clause,[],[f7611,f7502,f7654])).
% 3.50/0.84  fof(f7611,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) | ~spl4_283),
% 3.50/0.84    inference(superposition,[],[f20,f7503])).
% 3.50/0.84  fof(f7609,plain,(
% 3.50/0.84    spl4_283 | ~spl4_8),
% 3.50/0.84    inference(avatar_split_clause,[],[f7358,f130,f7502])).
% 3.50/0.84  fof(f130,plain,(
% 3.50/0.84    spl4_8 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.50/0.84  fof(f7358,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1)) | ~spl4_8),
% 3.50/0.84    inference(superposition,[],[f131,f1229])).
% 3.50/0.84  fof(f1229,plain,(
% 3.50/0.84    ( ! [X6,X4,X7,X5] : (k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)) = k3_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X4,X7))) )),
% 3.50/0.84    inference(superposition,[],[f245,f28])).
% 3.50/0.84  fof(f28,plain,(
% 3.50/0.84    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.50/0.84    inference(cnf_transformation,[],[f6])).
% 3.50/0.84  fof(f6,axiom,(
% 3.50/0.84    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.50/0.84  fof(f245,plain,(
% 3.50/0.84    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X1,X0),k3_xboole_0(X2,X3))) )),
% 3.50/0.84    inference(superposition,[],[f28,f21])).
% 3.50/0.84  fof(f131,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl4_8),
% 3.50/0.84    inference(avatar_component_clause,[],[f130])).
% 3.50/0.84  fof(f973,plain,(
% 3.50/0.84    spl4_55),
% 3.50/0.84    inference(avatar_contradiction_clause,[],[f972])).
% 3.50/0.84  fof(f972,plain,(
% 3.50/0.84    $false | spl4_55),
% 3.50/0.84    inference(trivial_inequality_removal,[],[f971])).
% 3.50/0.84  fof(f971,plain,(
% 3.50/0.84    k1_xboole_0 != k1_xboole_0 | spl4_55),
% 3.50/0.84    inference(superposition,[],[f889,f30])).
% 3.50/0.84  fof(f30,plain,(
% 3.50/0.84    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.50/0.84    inference(equality_resolution,[],[f24])).
% 3.50/0.84  fof(f24,plain,(
% 3.50/0.84    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.50/0.84    inference(cnf_transformation,[],[f16])).
% 3.50/0.84  fof(f16,plain,(
% 3.50/0.84    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.84    inference(flattening,[],[f15])).
% 3.50/0.84  fof(f15,plain,(
% 3.50/0.84    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.84    inference(nnf_transformation,[],[f4])).
% 3.50/0.84  fof(f4,axiom,(
% 3.50/0.84    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.50/0.84  fof(f889,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl4_55),
% 3.50/0.84    inference(avatar_component_clause,[],[f888])).
% 3.50/0.84  fof(f888,plain,(
% 3.50/0.84    spl4_55 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 3.50/0.84  fof(f890,plain,(
% 3.50/0.84    ~spl4_55 | spl4_3 | ~spl4_41),
% 3.50/0.84    inference(avatar_split_clause,[],[f854,f785,f39,f888])).
% 3.50/0.84  fof(f39,plain,(
% 3.50/0.84    spl4_3 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.50/0.84  fof(f854,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl4_3 | ~spl4_41)),
% 3.50/0.84    inference(superposition,[],[f40,f786])).
% 3.50/0.84  fof(f786,plain,(
% 3.50/0.84    k1_xboole_0 = sK0 | ~spl4_41),
% 3.50/0.84    inference(avatar_component_clause,[],[f785])).
% 3.50/0.84  fof(f40,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl4_3),
% 3.50/0.84    inference(avatar_component_clause,[],[f39])).
% 3.50/0.84  fof(f597,plain,(
% 3.50/0.84    spl4_21),
% 3.50/0.84    inference(avatar_contradiction_clause,[],[f596])).
% 3.50/0.84  fof(f596,plain,(
% 3.50/0.84    $false | spl4_21),
% 3.50/0.84    inference(trivial_inequality_removal,[],[f595])).
% 3.50/0.84  fof(f595,plain,(
% 3.50/0.84    k1_xboole_0 != k1_xboole_0 | spl4_21),
% 3.50/0.84    inference(superposition,[],[f439,f29])).
% 3.50/0.84  fof(f29,plain,(
% 3.50/0.84    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.50/0.84    inference(equality_resolution,[],[f25])).
% 3.50/0.84  fof(f25,plain,(
% 3.50/0.84    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.50/0.84    inference(cnf_transformation,[],[f16])).
% 3.50/0.84  fof(f439,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl4_21),
% 3.50/0.84    inference(avatar_component_clause,[],[f438])).
% 3.50/0.84  fof(f438,plain,(
% 3.50/0.84    spl4_21 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 3.50/0.84  fof(f440,plain,(
% 3.50/0.84    ~spl4_21 | spl4_3 | ~spl4_13),
% 3.50/0.84    inference(avatar_split_clause,[],[f425,f395,f39,f438])).
% 3.50/0.84  fof(f425,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl4_3 | ~spl4_13)),
% 3.50/0.84    inference(superposition,[],[f40,f396])).
% 3.50/0.84  fof(f396,plain,(
% 3.50/0.84    k1_xboole_0 = sK1 | ~spl4_13),
% 3.50/0.84    inference(avatar_component_clause,[],[f395])).
% 3.50/0.84  fof(f132,plain,(
% 3.50/0.84    spl4_8 | ~spl4_5),
% 3.50/0.84    inference(avatar_split_clause,[],[f119,f54,f130])).
% 3.50/0.84  fof(f54,plain,(
% 3.50/0.84    spl4_5 <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.50/0.84  fof(f119,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 3.50/0.84    inference(superposition,[],[f95,f55])).
% 3.50/0.84  fof(f55,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_5),
% 3.50/0.84    inference(avatar_component_clause,[],[f54])).
% 3.50/0.84  fof(f95,plain,(
% 3.50/0.84    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 3.50/0.84    inference(superposition,[],[f52,f21])).
% 3.50/0.84  fof(f52,plain,(
% 3.50/0.84    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 3.50/0.84    inference(resolution,[],[f22,f46])).
% 3.50/0.84  fof(f56,plain,(
% 3.50/0.84    spl4_5 | ~spl4_4),
% 3.50/0.84    inference(avatar_split_clause,[],[f50,f43,f54])).
% 3.50/0.84  fof(f43,plain,(
% 3.50/0.84    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.50/0.84    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.50/0.84  fof(f50,plain,(
% 3.50/0.84    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_4),
% 3.50/0.84    inference(resolution,[],[f22,f44])).
% 3.50/0.84  fof(f44,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_4),
% 3.50/0.84    inference(avatar_component_clause,[],[f43])).
% 3.50/0.84  fof(f45,plain,(
% 3.50/0.84    spl4_4),
% 3.50/0.84    inference(avatar_split_clause,[],[f17,f43])).
% 3.50/0.84  fof(f17,plain,(
% 3.50/0.84    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.50/0.84    inference(cnf_transformation,[],[f14])).
% 3.50/0.84  fof(f14,plain,(
% 3.50/0.84    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.50/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).
% 3.50/0.84  fof(f13,plain,(
% 3.50/0.84    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 3.50/0.84    introduced(choice_axiom,[])).
% 3.50/0.84  fof(f10,plain,(
% 3.50/0.84    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0 & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.50/0.84    inference(flattening,[],[f9])).
% 3.50/0.84  fof(f9,plain,(
% 3.50/0.84    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k2_zfmisc_1(X0,X1) != k1_xboole_0) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.50/0.84    inference(ennf_transformation,[],[f8])).
% 3.50/0.84  fof(f8,negated_conjecture,(
% 3.50/0.84    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 3.50/0.84    inference(negated_conjecture,[],[f7])).
% 3.50/0.84  fof(f7,conjecture,(
% 3.50/0.84    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 3.50/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.50/0.84  fof(f41,plain,(
% 3.50/0.84    ~spl4_3),
% 3.50/0.84    inference(avatar_split_clause,[],[f18,f39])).
% 3.50/0.84  fof(f18,plain,(
% 3.50/0.84    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 3.50/0.84    inference(cnf_transformation,[],[f14])).
% 3.50/0.84  fof(f37,plain,(
% 3.50/0.84    ~spl4_1 | ~spl4_2),
% 3.50/0.84    inference(avatar_split_clause,[],[f19,f35,f32])).
% 3.50/0.84  fof(f19,plain,(
% 3.50/0.84    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 3.50/0.84    inference(cnf_transformation,[],[f14])).
% 3.50/0.84  % SZS output end Proof for theBenchmark
% 3.50/0.84  % (4347)------------------------------
% 3.50/0.84  % (4347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.84  % (4347)Termination reason: Refutation
% 3.50/0.84  
% 3.50/0.84  % (4347)Memory used [KB]: 15095
% 3.50/0.84  % (4347)Time elapsed: 0.365 s
% 3.50/0.84  % (4347)------------------------------
% 3.50/0.84  % (4347)------------------------------
% 3.50/0.84  % (4340)Success in time 0.482 s
%------------------------------------------------------------------------------
