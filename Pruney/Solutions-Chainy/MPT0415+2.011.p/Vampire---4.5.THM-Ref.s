%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 265 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  348 ( 731 expanded)
%              Number of equality atoms :   54 ( 166 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f100,f112,f190,f196,f204,f260,f271])).

fof(f271,plain,
    ( ~ spl6_5
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl6_5
    | spl6_8 ),
    inference(resolution,[],[f261,f202])).

fof(f202,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl6_8
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f261,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_5 ),
    inference(resolution,[],[f182,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f182,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_5
  <=> ! [X3] : ~ r2_hidden(X3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f260,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl6_8 ),
    inference(superposition,[],[f43,f216])).

fof(f216,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f212,f214])).

fof(f214,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(sK3,k3_xboole_0(sK3,X0))
    | ~ spl6_8 ),
    inference(resolution,[],[f211,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f211,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl6_8 ),
    inference(resolution,[],[f205,f61])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f203,f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f73,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_enumset1(X1,X1,X1))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f65,f48,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f203,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f212,plain,
    ( ! [X1] : sK3 = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_enumset1(X1,X1,X1)))
    | ~ spl6_8 ),
    inference(resolution,[],[f205,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k1_enumset1(X1,X1,X1))) = X0 ) ),
    inference(definition_unfolding,[],[f66,f48,f68])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f43,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK2,sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f204,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f197,f188,f80,f201])).

fof(f80,plain,
    ( spl6_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f188,plain,
    ( spl6_7
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))
        | ~ r2_hidden(sK5(sK3,k1_xboole_0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_7 ),
    inference(resolution,[],[f189,f61])).

fof(f189,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK3,k1_xboole_0),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f196,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl6_6 ),
    inference(resolution,[],[f186,f108])).

fof(f186,plain,
    ( r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_6
  <=> r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f190,plain,
    ( spl6_5
    | spl6_6
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f179,f93,f188,f184,f181])).

fof(f93,plain,
    ( spl6_3
  <=> sP0(sK3,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f179,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))
        | ~ r2_hidden(sK5(sK3,k1_xboole_0),X2)
        | r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0)
        | ~ r2_hidden(X3,sK3) )
    | ~ spl6_3 ),
    inference(resolution,[],[f159,f116])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK2)))
        | ~ r2_hidden(sK5(sK3,X0),X1)
        | r2_hidden(k3_subset_1(sK2,sK5(sK3,X0)),k1_xboole_0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f155,f61])).

fof(f155,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,sK3)
        | r2_hidden(k3_subset_1(sK2,X3),k1_xboole_0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
        | ~ r2_hidden(X3,X4) )
    | ~ spl6_3 ),
    inference(resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f142,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2))
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | ~ spl6_3 ),
    inference(superposition,[],[f139,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k3_subset_1(sK2,X0),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f55,f95])).

fof(f95,plain,
    ( sP0(sK3,sK2,k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(k3_subset_1(X1,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) )
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X2)
                | ~ r2_hidden(k3_subset_1(X1,X4),X0) )
              & ( r2_hidden(k3_subset_1(X1,X4),X0)
                | ~ r2_hidden(X4,X2) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k3_subset_1(X1,X3),X0)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X1,X3),X0)
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ( ~ r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X1,X3),X0)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X1,X3),X0)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( ( ( r2_hidden(X4,X2)
                | ~ r2_hidden(k3_subset_1(X1,X4),X0) )
              & ( r2_hidden(k3_subset_1(X1,X4),X0)
                | ~ r2_hidden(X4,X2) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X0,X3),X1)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
              & ( r2_hidden(k3_subset_1(X0,X3),X1)
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(k3_subset_1(X0,X3),X1)
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
              & ( r2_hidden(k3_subset_1(X0,X3),X1)
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> r2_hidden(k3_subset_1(X0,X3),X1) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f112,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f111,f97,f84,f80])).

fof(f84,plain,
    ( spl6_2
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f97,plain,
    ( spl6_4
  <=> sP1(k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f111,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | spl6_4 ),
    inference(resolution,[],[f59,f99])).

fof(f99,plain,
    ( ~ sP1(k1_xboole_0,sK2,sK3)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f20,f25,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f100,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f91,f97,f93])).

fof(f91,plain,
    ( ~ sP1(k1_xboole_0,sK2,sK3)
    | sP0(sK3,sK2,k1_xboole_0) ),
    inference(superposition,[],[f74,f44])).

fof(f44,plain,(
    k1_xboole_0 = k7_setfam_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ sP1(k7_setfam_1(X1,X2),X1,X2)
      | sP0(X2,X1,k7_setfam_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k7_setfam_1(X1,X2) != X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_setfam_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f90,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f78,f84,f80])).

fof(f78,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(superposition,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (17065)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (17072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (17073)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (17088)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (17067)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (17066)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (17077)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17080)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (17078)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (17076)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (17081)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (17069)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (17089)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (17079)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (17093)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (17071)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (17085)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (17086)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (17070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (17068)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (17087)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (17077)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f87,f90,f100,f112,f190,f196,f204,f260,f271])).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    ~spl6_5 | spl6_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f268])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    $false | (~spl6_5 | spl6_8)),
% 0.20/0.53    inference(resolution,[],[f261,f202])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k1_xboole_0) | spl6_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    spl6_8 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_5),
% 0.20/0.53    inference(resolution,[],[f182,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ( ! [X3] : (~r2_hidden(X3,sK3)) ) | ~spl6_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f181])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    spl6_5 <=> ! [X3] : ~r2_hidden(X3,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ~spl6_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f259])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    $false | ~spl6_8),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f258])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | ~spl6_8),
% 0.20/0.53    inference(superposition,[],[f43,f216])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | ~spl6_8),
% 0.20/0.53    inference(backward_demodulation,[],[f212,f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) ) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f211,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f64,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f205,f61])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f203,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r1_tarski(X3,k1_xboole_0) | ~r2_hidden(X2,X3)) )),
% 0.20/0.53    inference(resolution,[],[f108,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f73,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f45,f48])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_enumset1(X1,X1,X1))) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f65,f48,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    r1_tarski(sK3,k1_xboole_0) | ~spl6_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f201])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ( ! [X1] : (sK3 = k5_xboole_0(sK3,k3_xboole_0(sK3,k1_enumset1(X1,X1,X1)))) ) | ~spl6_8),
% 0.20/0.53    inference(resolution,[],[f205,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k1_enumset1(X1,X1,X1))) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f66,f48,f68])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    k1_xboole_0 != sK3),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK2,sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    spl6_8 | ~spl6_1 | ~spl6_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f197,f188,f80,f201])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    spl6_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    spl6_7 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(sK5(sK3,k1_xboole_0),X2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | r1_tarski(sK3,k1_xboole_0) | ~spl6_7),
% 0.20/0.53    inference(resolution,[],[f189,f61])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X2] : (~r2_hidden(sK5(sK3,k1_xboole_0),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) ) | ~spl6_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f188])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    ~spl6_6),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f192])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    $false | ~spl6_6),
% 0.20/0.53    inference(resolution,[],[f186,f108])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0) | ~spl6_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f184])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    spl6_6 <=> r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    spl6_5 | spl6_6 | spl6_7 | ~spl6_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f179,f93,f188,f184,f181])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl6_3 <=> sP0(sK3,sK2,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(sK5(sK3,k1_xboole_0),X2) | r2_hidden(k3_subset_1(sK2,sK5(sK3,k1_xboole_0)),k1_xboole_0) | ~r2_hidden(X3,sK3)) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f159,f116])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(sK3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(sK5(sK3,X0),X1) | r2_hidden(k3_subset_1(sK2,sK5(sK3,X0)),k1_xboole_0)) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f155,f61])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    ( ! [X4,X3] : (~r2_hidden(X3,sK3) | r2_hidden(k3_subset_1(sK2,X3),k1_xboole_0) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~r2_hidden(X3,X4)) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f152,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0) | ~r2_hidden(X0,sK3)) ) | ~spl6_3),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f148])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f142,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(k3_subset_1(sK2,X0),k1_zfmisc_1(sK2)) | ~r2_hidden(X0,sK3) | r2_hidden(k3_subset_1(sK2,X0),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(sK2))) ) | ~spl6_3),
% 0.20/0.53    inference(superposition,[],[f139,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(k3_subset_1(sK2,X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f55,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    sP0(sK3,sK2,k1_xboole_0) | ~spl6_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | r2_hidden(X4,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1))) => ((~r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(k3_subset_1(X1,sK4(X0,X1,X2)),X0) | r2_hidden(sK4(X0,X1,X2),X2)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X1,X3),X0) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X1,X3),X0) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (((r2_hidden(X4,X2) | ~r2_hidden(k3_subset_1(X1,X4),X0)) & (r2_hidden(k3_subset_1(X1,X4),X0) | ~r2_hidden(X4,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP0(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ~spl6_1 | ~spl6_2 | spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f111,f97,f84,f80])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl6_2 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl6_4 <=> sP1(k1_xboole_0,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | spl6_4),
% 0.20/0.53    inference(resolution,[],[f59,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ~sP1(k1_xboole_0,sK2,sK3) | spl6_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f97])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (sP1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(definition_folding,[],[f20,f25,f24])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X2,X0,X1] : ((k7_setfam_1(X0,X1) = X2 <=> sP0(X1,X0,X2)) | ~sP1(X2,X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    spl6_3 | ~spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f91,f97,f93])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ~sP1(k1_xboole_0,sK2,sK3) | sP0(sK3,sK2,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f74,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    k1_xboole_0 = k7_setfam_1(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~sP1(k7_setfam_1(X1,X2),X1,X2) | sP0(X2,X1,k7_setfam_1(X1,X2))) )),
% 0.20/0.53    inference(equality_resolution,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0 | ~sP1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((k7_setfam_1(X1,X2) = X0 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k7_setfam_1(X1,X2) != X0)) | ~sP1(X0,X1,X2))),
% 0.20/0.53    inference(rectify,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X2,X0,X1] : (((k7_setfam_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k7_setfam_1(X0,X1) != X2)) | ~sP1(X2,X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f25])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    spl6_1),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    $false | spl6_1),
% 0.20/0.53    inference(resolution,[],[f82,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | spl6_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f80])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ~spl6_1 | spl6_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f78,f84,f80])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.20/0.53    inference(superposition,[],[f51,f44])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (17077)------------------------------
% 0.20/0.53  % (17077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (17077)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (17077)Memory used [KB]: 6396
% 0.20/0.53  % (17077)Time elapsed: 0.116 s
% 0.20/0.53  % (17077)------------------------------
% 0.20/0.53  % (17077)------------------------------
% 0.20/0.53  % (17091)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (17064)Success in time 0.182 s
%------------------------------------------------------------------------------
