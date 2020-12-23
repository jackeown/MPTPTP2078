%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 363 expanded)
%              Number of leaves         :   40 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          :  404 ( 781 expanded)
%              Number of equality atoms :  130 ( 323 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f133,f138,f143,f148,f167,f173,f189,f205,f223,f232,f233,f272])).

fof(f272,plain,(
    ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f116,f266,f117])).

fof(f117,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f266,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl5_13 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f264,f63])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f264,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f261,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f62,f104])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f103])).

fof(f103,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f69,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f94,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f96,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f97,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f261,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl5_13 ),
    inference(superposition,[],[f241,f110])).

fof(f110,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f67,f103,f103])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f241,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)))
        | ~ r2_hidden(sK0,X4) )
    | ~ spl5_13 ),
    inference(superposition,[],[f112,f211])).

fof(f211,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl5_13
  <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f106,f105,f106])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f70,f104])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f103])).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f233,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f232,plain,
    ( ~ spl5_16
    | spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f226,f220,f209,f229])).

fof(f229,plain,
    ( spl5_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f220,plain,
    ( spl5_15
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f226,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f224,f59])).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f224,plain,
    ( k1_relat_1(k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_15 ),
    inference(superposition,[],[f222,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f222,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( spl5_2
    | ~ spl5_12
    | spl5_15
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f218,f186,f145,f220,f202,f130])).

fof(f130,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f202,plain,
    ( spl5_12
  <=> v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f145,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f186,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f218,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f217,f188])).

fof(f188,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f217,plain,
    ( ~ v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f150,f188])).

fof(f150,plain,
    ( ~ v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | k1_xboole_0 = sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f147,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f205,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f177,f161,f140,f202])).

fof(f140,plain,
    ( spl5_4
  <=> v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f161,plain,
    ( spl5_6
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f177,plain,
    ( v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f142,f174])).

fof(f174,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_6 ),
    inference(resolution,[],[f162,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f162,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f142,plain,
    ( v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f189,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f174,f161,f186])).

fof(f173,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f166,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

% (27908)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f166,plain,
    ( r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f137,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f132,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f127,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f167,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f159,f145,f164,f161])).

fof(f159,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_5 ),
    inference(superposition,[],[f156,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f153,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f91,f106])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f153,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f147,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f156,plain,
    ( ! [X2] :
        ( r2_hidden(k1_mcart_1(X2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f153,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f148,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f107,f145])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f56,f106])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f143,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f108,f140])).

fof(f108,plain,(
    v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f55,f106])).

fof(f55,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f138,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f135])).

fof(f58,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f130])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f128,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (27898)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (27901)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (27903)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (27902)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (27899)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (27907)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (27920)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (27911)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (27905)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (27897)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (27910)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (27904)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (27921)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (27927)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (27900)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (27917)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (27923)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (27926)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (27922)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (27915)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (27898)Refutation not found, incomplete strategy% (27898)------------------------------
% 0.20/0.54  % (27898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27898)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27898)Memory used [KB]: 1663
% 0.20/0.54  % (27898)Time elapsed: 0.127 s
% 0.20/0.54  % (27898)------------------------------
% 0.20/0.54  % (27898)------------------------------
% 0.20/0.54  % (27911)Refutation not found, incomplete strategy% (27911)------------------------------
% 0.20/0.54  % (27911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27911)Memory used [KB]: 1791
% 0.20/0.54  % (27911)Time elapsed: 0.063 s
% 0.20/0.54  % (27911)------------------------------
% 0.20/0.54  % (27911)------------------------------
% 0.20/0.55  % (27925)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (27928)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (27914)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (27928)Refutation not found, incomplete strategy% (27928)------------------------------
% 0.20/0.55  % (27928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27928)Memory used [KB]: 1663
% 0.20/0.55  % (27928)Time elapsed: 0.117 s
% 0.20/0.55  % (27928)------------------------------
% 0.20/0.55  % (27928)------------------------------
% 0.20/0.55  % (27914)Refutation not found, incomplete strategy% (27914)------------------------------
% 0.20/0.55  % (27914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27914)Memory used [KB]: 10746
% 0.20/0.55  % (27914)Time elapsed: 0.130 s
% 0.20/0.55  % (27914)------------------------------
% 0.20/0.55  % (27914)------------------------------
% 0.20/0.55  % (27918)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (27913)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (27906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (27907)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f273,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f128,f133,f138,f143,f148,f167,f173,f189,f205,f223,f232,f233,f272])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    ~spl5_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f270])).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    $false | ~spl5_13),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f116,f266,f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.55  fof(f266,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | ~spl5_13),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f265])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,X0)) ) | ~spl5_13),
% 0.20/0.55    inference(forward_demodulation,[],[f264,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.55  fof(f264,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK0,X0)) ) | ~spl5_13),
% 0.20/0.55    inference(forward_demodulation,[],[f261,f109])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f62,f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f68,f103])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f69,f102])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f81,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f94,f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f96,f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f97,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.55  fof(f261,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) | ~r2_hidden(sK0,X0)) ) | ~spl5_13),
% 0.20/0.55    inference(superposition,[],[f241,f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f67,f103,f103])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ( ! [X4] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) | ~r2_hidden(sK0,X4)) ) | ~spl5_13),
% 0.20/0.55    inference(superposition,[],[f112,f211])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f209])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    spl5_13 <=> k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f79,f106,f105,f106])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f70,f104])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f64,f103])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    ~spl5_16 | spl5_13 | ~spl5_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f226,f220,f209,f229])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    spl5_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    spl5_15 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | ~spl5_15),
% 0.20/0.55    inference(forward_demodulation,[],[f224,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,axiom,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    k1_relat_1(k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | ~spl5_15),
% 0.20/0.55    inference(superposition,[],[f222,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~spl5_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f220])).
% 0.20/0.55  fof(f223,plain,(
% 0.20/0.55    spl5_2 | ~spl5_12 | spl5_15 | ~spl5_5 | ~spl5_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f218,f186,f145,f220,f202,f130])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    spl5_2 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    spl5_12 <=> v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    spl5_9 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | (~spl5_5 | ~spl5_9)),
% 0.20/0.55    inference(forward_demodulation,[],[f217,f188])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl5_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f186])).
% 0.20/0.55  fof(f217,plain,(
% 0.20/0.55    ~v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) | (~spl5_5 | ~spl5_9)),
% 0.20/0.55    inference(forward_demodulation,[],[f150,f188])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | k1_xboole_0 = sK1 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) | ~spl5_5),
% 0.20/0.55    inference(resolution,[],[f147,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f147,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | ~spl5_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f145])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    spl5_12 | ~spl5_4 | ~spl5_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f177,f161,f140,f202])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    spl5_4 <=> v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    spl5_6 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    v1_funct_2(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | (~spl5_4 | ~spl5_6)),
% 0.20/0.55    inference(backward_demodulation,[],[f142,f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl5_6),
% 0.20/0.55    inference(resolution,[],[f162,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f161])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f140])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    spl5_9 | ~spl5_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f174,f161,f186])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f172])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    $false | (~spl5_1 | spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f127,f132,f137,f142,f147,f166,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f26])).
% 0.20/0.55  % (27908)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  fof(f26,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f164])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    spl5_7 <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl5_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    spl5_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl5_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f130])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    v1_funct_1(sK2) | ~spl5_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f125])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    spl5_1 <=> v1_funct_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    spl5_6 | spl5_7 | ~spl5_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f159,f145,f164,f161])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl5_5),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f158])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl5_5),
% 0.20/0.55    inference(superposition,[],[f156,f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl5_5),
% 0.20/0.55    inference(resolution,[],[f153,f114])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f91,f106])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl5_5),
% 0.20/0.55    inference(resolution,[],[f147,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl5_5),
% 0.20/0.55    inference(resolution,[],[f153,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    spl5_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f107,f145])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 0.20/0.55    inference(definition_unfolding,[],[f56,f106])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f27])).
% 0.20/0.55  fof(f27,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    spl5_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f108,f140])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.20/0.55    inference(definition_unfolding,[],[f55,f106])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ~spl5_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f58,f135])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ~spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f57,f130])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    spl5_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f54,f125])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (27907)------------------------------
% 0.20/0.55  % (27907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27907)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (27907)Memory used [KB]: 10874
% 0.20/0.55  % (27907)Time elapsed: 0.140 s
% 0.20/0.55  % (27907)------------------------------
% 0.20/0.55  % (27907)------------------------------
% 0.20/0.55  % (27890)Success in time 0.189 s
%------------------------------------------------------------------------------
