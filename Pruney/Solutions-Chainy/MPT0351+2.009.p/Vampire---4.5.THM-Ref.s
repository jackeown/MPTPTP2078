%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:04 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 261 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  320 ( 531 expanded)
%              Number of equality atoms :   65 ( 192 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f245,f262,f762,f769])).

fof(f769,plain,
    ( ~ spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f767,f244])).

fof(f244,plain,
    ( r1_tarski(sK4,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl8_4
  <=> r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f767,plain,
    ( ~ r1_tarski(sK4,sK3)
    | spl8_10 ),
    inference(trivial_inequality_removal,[],[f763])).

fof(f763,plain,
    ( sK3 != sK3
    | ~ r1_tarski(sK4,sK3)
    | spl8_10 ),
    inference(superposition,[],[f759,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f92,f116])).

fof(f116,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f65,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f58,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f81,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f82,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f759,plain,
    ( sK3 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl8_10
  <=> sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f762,plain,
    ( spl8_3
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f761,f757,f239])).

fof(f239,plain,
    ( spl8_3
  <=> ! [X4] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f761,plain,(
    ! [X5] :
      ( sK3 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X5)) ) ),
    inference(forward_demodulation,[],[f748,f91])).

fof(f91,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f56,f89,f89])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f748,plain,(
    ! [X5] :
      ( sK3 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f747])).

fof(f747,plain,(
    ! [X5] :
      ( sK3 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f741,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f90])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f741,plain,(
    ! [X0] :
      ( sK3 != k4_subset_1(X0,sK4,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f740,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
    & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))
      & m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

fof(f740,plain,(
    ! [X0] :
      ( sK3 != k4_subset_1(X0,sK4,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f666,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f666,plain,(
    ! [X0] :
      ( sK3 != k4_subset_1(X0,sK4,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(sK3)) ) ),
    inference(superposition,[],[f95,f299])).

fof(f299,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_subset_1(X5,X3,X4) = k4_subset_1(X6,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f93,f93])).

fof(f95,plain,(
    sK3 != k4_subset_1(sK3,sK4,sK3) ),
    inference(backward_demodulation,[],[f51,f53])).

fof(f51,plain,(
    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f262,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f257,f97])).

fof(f257,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl8_3 ),
    inference(resolution,[],[f240,f50])).

fof(f240,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X4)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f239])).

fof(f245,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f234,f242,f239])).

fof(f234,plain,(
    ! [X4] :
      ( r1_tarski(sK4,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f69,f159])).

fof(f159,plain,(
    ! [X0] : ~ sP0(sK3,sK4,X0) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ sP0(sK3,sK4,X0)
      | ~ sP0(sK3,sK4,X0) ) ),
    inference(resolution,[],[f157,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
     => ( ~ r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(sK3,X0,X1),sK4)
      | ~ sP0(sK3,X0,X1) ) ),
    inference(resolution,[],[f153,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f153,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f137,f111])).

fof(f111,plain,(
    r2_hidden(sK4,k1_zfmisc_1(sK3)) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f108,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(sK3))
    | v1_xboole_0(k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f76,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ sP1(k1_zfmisc_1(X2),X3)
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f71,f96])).

fof(f96,plain,(
    ! [X0] : sP2(k1_zfmisc_1(X0),X0) ),
    inference(superposition,[],[f94,f54])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f94,plain,(
    ! [X0] : sP2(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f11,f32,f31])).

fof(f31,plain,(
    ! [X0,X2] :
      ( sP1(X0,X2)
    <=> ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP1(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X0,X3)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( ~ sP1(X0,sK6(X0,X1))
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sP1(X0,sK6(X0,X1))
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP1(X0,X3) )
            & ( sP1(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP1(X0,X2)
            | ~ r2_hidden(X2,X1) )
          & ( sP1(X0,X2)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP1(X0,sK6(X0,X1))
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sP1(X0,sK6(X0,X1))
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( ~ sP1(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP1(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP1(X0,X3) )
            & ( sP1(X0,X3)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( ~ sP1(X0,X2)
              | ~ r2_hidden(X2,X1) )
            & ( sP1(X0,X2)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP1(X0,X2) )
            & ( sP1(X0,X2)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ( r2_hidden(sK7(X0,X1),X0)
          & r2_hidden(X1,sK7(X0,X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r2_hidden(X1,X3) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(X1,sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X2) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X1,X3) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2] :
      ( ( sP1(X0,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X3) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X0)
            & r2_hidden(X2,X3) )
        | ~ sP1(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | sP0(X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f26,f29])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.52  % (19382)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (19379)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (19398)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (19381)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (19380)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19378)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (19398)Refutation not found, incomplete strategy% (19398)------------------------------
% 0.21/0.55  % (19398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19398)Memory used [KB]: 10746
% 0.21/0.55  % (19398)Time elapsed: 0.113 s
% 0.21/0.55  % (19398)------------------------------
% 0.21/0.55  % (19398)------------------------------
% 0.21/0.55  % (19390)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (19397)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (19385)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (19397)Refutation not found, incomplete strategy% (19397)------------------------------
% 0.21/0.55  % (19397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19397)Memory used [KB]: 1791
% 0.21/0.55  % (19397)Time elapsed: 0.132 s
% 0.21/0.55  % (19397)------------------------------
% 0.21/0.55  % (19397)------------------------------
% 0.21/0.55  % (19387)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (19384)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (19387)Refutation not found, incomplete strategy% (19387)------------------------------
% 0.21/0.55  % (19387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19389)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.56  % (19388)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.56  % (19401)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.56  % (19376)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.56  % (19395)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.56  % (19405)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.56  % (19404)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.56  % (19403)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.56  % (19387)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (19387)Memory used [KB]: 10618
% 1.30/0.56  % (19387)Time elapsed: 0.126 s
% 1.30/0.56  % (19387)------------------------------
% 1.30/0.56  % (19387)------------------------------
% 1.30/0.56  % (19386)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.57  % (19394)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.57  % (19377)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.57  % (19392)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.57  % (19396)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.57  % (19396)Refutation not found, incomplete strategy% (19396)------------------------------
% 1.30/0.57  % (19396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (19396)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (19396)Memory used [KB]: 10746
% 1.30/0.57  % (19396)Time elapsed: 0.147 s
% 1.30/0.57  % (19396)------------------------------
% 1.30/0.57  % (19396)------------------------------
% 1.59/0.57  % (19400)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.58  % (19386)Refutation not found, incomplete strategy% (19386)------------------------------
% 1.59/0.58  % (19386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (19399)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.59/0.58  % (19386)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (19386)Memory used [KB]: 10618
% 1.59/0.58  % (19386)Time elapsed: 0.146 s
% 1.59/0.58  % (19386)------------------------------
% 1.59/0.58  % (19386)------------------------------
% 1.59/0.58  % (19391)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.59/0.58  % (19393)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.58  % (19383)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.59/0.59  % (19402)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.61  % (19402)Refutation not found, incomplete strategy% (19402)------------------------------
% 1.59/0.61  % (19402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (19402)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (19402)Memory used [KB]: 10746
% 1.59/0.61  % (19402)Time elapsed: 0.166 s
% 1.59/0.61  % (19402)------------------------------
% 1.59/0.61  % (19402)------------------------------
% 1.59/0.62  % (19403)Refutation found. Thanks to Tanya!
% 1.59/0.62  % SZS status Theorem for theBenchmark
% 1.59/0.62  % SZS output start Proof for theBenchmark
% 1.59/0.62  fof(f770,plain,(
% 1.59/0.62    $false),
% 1.59/0.62    inference(avatar_sat_refutation,[],[f245,f262,f762,f769])).
% 1.59/0.62  fof(f769,plain,(
% 1.59/0.62    ~spl8_4 | spl8_10),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f768])).
% 1.59/0.62  fof(f768,plain,(
% 1.59/0.62    $false | (~spl8_4 | spl8_10)),
% 1.59/0.62    inference(subsumption_resolution,[],[f767,f244])).
% 1.59/0.62  fof(f244,plain,(
% 1.59/0.62    r1_tarski(sK4,sK3) | ~spl8_4),
% 1.59/0.62    inference(avatar_component_clause,[],[f242])).
% 1.59/0.62  fof(f242,plain,(
% 1.59/0.62    spl8_4 <=> r1_tarski(sK4,sK3)),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.59/0.62  fof(f767,plain,(
% 1.59/0.62    ~r1_tarski(sK4,sK3) | spl8_10),
% 1.59/0.62    inference(trivial_inequality_removal,[],[f763])).
% 1.59/0.62  fof(f763,plain,(
% 1.59/0.62    sK3 != sK3 | ~r1_tarski(sK4,sK3) | spl8_10),
% 1.59/0.62    inference(superposition,[],[f759,f185])).
% 1.59/0.62  fof(f185,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X1,X0)) )),
% 1.59/0.62    inference(superposition,[],[f92,f116])).
% 1.59/0.62  fof(f116,plain,(
% 1.59/0.62    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.59/0.62    inference(superposition,[],[f65,f57])).
% 1.59/0.62  fof(f57,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f1])).
% 1.59/0.62  fof(f1,axiom,(
% 1.59/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.62  fof(f65,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f24])).
% 1.59/0.62  fof(f24,plain,(
% 1.59/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.62    inference(ennf_transformation,[],[f3])).
% 1.59/0.62  fof(f3,axiom,(
% 1.59/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.62  fof(f92,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.59/0.62    inference(definition_unfolding,[],[f58,f90])).
% 1.59/0.62  fof(f90,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f60,f89])).
% 1.59/0.62  fof(f89,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f59,f88])).
% 1.59/0.62  fof(f88,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f79,f87])).
% 1.59/0.62  fof(f87,plain,(
% 1.59/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f81,f86])).
% 1.59/0.62  fof(f86,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f82,f85])).
% 1.59/0.62  fof(f85,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f83,f84])).
% 1.59/0.62  fof(f84,plain,(
% 1.59/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f10])).
% 1.59/0.62  fof(f10,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.59/0.62  fof(f83,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f9])).
% 1.59/0.62  fof(f9,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.59/0.62  fof(f82,plain,(
% 1.59/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f8])).
% 1.59/0.62  fof(f8,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.59/0.62  fof(f81,plain,(
% 1.59/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f7])).
% 1.59/0.62  fof(f7,axiom,(
% 1.59/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.59/0.62  fof(f79,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f6])).
% 1.59/0.62  fof(f6,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.62  fof(f59,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f5])).
% 1.59/0.62  fof(f5,axiom,(
% 1.59/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.62  fof(f60,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f12])).
% 1.59/0.62  fof(f12,axiom,(
% 1.59/0.62    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.59/0.62  fof(f58,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.59/0.62    inference(cnf_transformation,[],[f2])).
% 1.59/0.62  fof(f2,axiom,(
% 1.59/0.62    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.59/0.62  fof(f759,plain,(
% 1.59/0.62    sK3 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | spl8_10),
% 1.59/0.62    inference(avatar_component_clause,[],[f757])).
% 1.59/0.62  fof(f757,plain,(
% 1.59/0.62    spl8_10 <=> sK3 = k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.59/0.62  fof(f762,plain,(
% 1.59/0.62    spl8_3 | ~spl8_10),
% 1.59/0.62    inference(avatar_split_clause,[],[f761,f757,f239])).
% 1.59/0.62  fof(f239,plain,(
% 1.59/0.62    spl8_3 <=> ! [X4] : (~m1_subset_1(sK3,k1_zfmisc_1(X4)) | ~m1_subset_1(sK4,k1_zfmisc_1(X4)))),
% 1.59/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.59/0.62  fof(f761,plain,(
% 1.59/0.62    ( ! [X5] : (sK3 != k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(X5)) | ~m1_subset_1(sK4,k1_zfmisc_1(X5))) )),
% 1.59/0.62    inference(forward_demodulation,[],[f748,f91])).
% 1.59/0.62  fof(f91,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.59/0.62    inference(definition_unfolding,[],[f56,f89,f89])).
% 1.59/0.62  fof(f56,plain,(
% 1.59/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f4])).
% 1.59/0.62  fof(f4,axiom,(
% 1.59/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.62  fof(f748,plain,(
% 1.59/0.62    ( ! [X5] : (sK3 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X5)) | ~m1_subset_1(sK4,k1_zfmisc_1(X5))) )),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f747])).
% 1.59/0.62  fof(f747,plain,(
% 1.59/0.62    ( ! [X5] : (sK3 != k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(X5)) | ~m1_subset_1(sK4,k1_zfmisc_1(X5)) | ~m1_subset_1(sK3,k1_zfmisc_1(X5)) | ~m1_subset_1(sK4,k1_zfmisc_1(X5))) )),
% 1.59/0.62    inference(superposition,[],[f741,f93])).
% 1.59/0.62  fof(f93,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.62    inference(definition_unfolding,[],[f80,f90])).
% 1.59/0.62  fof(f80,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f28])).
% 1.59/0.62  fof(f28,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.62    inference(flattening,[],[f27])).
% 1.59/0.62  fof(f27,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.59/0.62    inference(ennf_transformation,[],[f18])).
% 1.59/0.62  fof(f18,axiom,(
% 1.59/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.59/0.62  fof(f741,plain,(
% 1.59/0.62    ( ! [X0] : (sK3 != k4_subset_1(X0,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(X0))) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f740,f50])).
% 1.59/0.62  fof(f50,plain,(
% 1.59/0.62    m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 1.59/0.62    inference(cnf_transformation,[],[f35])).
% 1.59/0.62  fof(f35,plain,(
% 1.59/0.62    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3))),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f34])).
% 1.59/0.62  fof(f34,plain,(
% 1.59/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3)) & m1_subset_1(sK4,k1_zfmisc_1(sK3)))),
% 1.59/0.62    introduced(choice_axiom,[])).
% 1.59/0.62  fof(f22,plain,(
% 1.59/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.62    inference(ennf_transformation,[],[f21])).
% 1.59/0.62  fof(f21,negated_conjecture,(
% 1.59/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.59/0.62    inference(negated_conjecture,[],[f20])).
% 1.59/0.62  fof(f20,conjecture,(
% 1.59/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).
% 1.59/0.62  fof(f740,plain,(
% 1.59/0.62    ( ! [X0] : (sK3 != k4_subset_1(X0,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(sK3))) )),
% 1.59/0.62    inference(subsumption_resolution,[],[f666,f97])).
% 1.59/0.62  fof(f97,plain,(
% 1.59/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.59/0.62    inference(forward_demodulation,[],[f55,f53])).
% 1.59/0.62  fof(f53,plain,(
% 1.59/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.59/0.62    inference(cnf_transformation,[],[f15])).
% 1.59/0.62  fof(f15,axiom,(
% 1.59/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.59/0.62  fof(f55,plain,(
% 1.59/0.62    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.59/0.62    inference(cnf_transformation,[],[f16])).
% 1.59/0.62  fof(f16,axiom,(
% 1.59/0.62    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.59/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.59/0.62  fof(f666,plain,(
% 1.59/0.62    ( ! [X0] : (sK3 != k4_subset_1(X0,sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(sK3))) )),
% 1.59/0.62    inference(superposition,[],[f95,f299])).
% 1.59/0.62  fof(f299,plain,(
% 1.59/0.62    ( ! [X6,X4,X5,X3] : (k4_subset_1(X5,X3,X4) = k4_subset_1(X6,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X3,k1_zfmisc_1(X6)) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | ~m1_subset_1(X3,k1_zfmisc_1(X5))) )),
% 1.59/0.62    inference(superposition,[],[f93,f93])).
% 1.59/0.62  fof(f95,plain,(
% 1.59/0.62    sK3 != k4_subset_1(sK3,sK4,sK3)),
% 1.59/0.62    inference(backward_demodulation,[],[f51,f53])).
% 1.59/0.62  fof(f51,plain,(
% 1.59/0.62    k2_subset_1(sK3) != k4_subset_1(sK3,sK4,k2_subset_1(sK3))),
% 1.59/0.62    inference(cnf_transformation,[],[f35])).
% 1.59/0.62  fof(f262,plain,(
% 1.59/0.62    ~spl8_3),
% 1.59/0.62    inference(avatar_contradiction_clause,[],[f261])).
% 1.59/0.62  fof(f261,plain,(
% 1.59/0.62    $false | ~spl8_3),
% 1.59/0.62    inference(subsumption_resolution,[],[f257,f97])).
% 1.59/0.62  fof(f257,plain,(
% 1.59/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(sK3)) | ~spl8_3),
% 1.59/0.62    inference(resolution,[],[f240,f50])).
% 1.59/0.62  fof(f240,plain,(
% 1.59/0.62    ( ! [X4] : (~m1_subset_1(sK4,k1_zfmisc_1(X4)) | ~m1_subset_1(sK3,k1_zfmisc_1(X4))) ) | ~spl8_3),
% 1.59/0.62    inference(avatar_component_clause,[],[f239])).
% 1.59/0.62  fof(f245,plain,(
% 1.59/0.62    spl8_3 | spl8_4),
% 1.59/0.62    inference(avatar_split_clause,[],[f234,f242,f239])).
% 1.59/0.62  fof(f234,plain,(
% 1.59/0.62    ( ! [X4] : (r1_tarski(sK4,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(X4)) | ~m1_subset_1(sK4,k1_zfmisc_1(X4))) )),
% 1.59/0.62    inference(resolution,[],[f69,f159])).
% 1.59/0.62  fof(f159,plain,(
% 1.59/0.62    ( ! [X0] : (~sP0(sK3,sK4,X0)) )),
% 1.59/0.62    inference(duplicate_literal_removal,[],[f158])).
% 1.59/0.62  fof(f158,plain,(
% 1.59/0.62    ( ! [X0] : (~sP0(sK3,sK4,X0) | ~sP0(sK3,sK4,X0)) )),
% 1.59/0.62    inference(resolution,[],[f157,f67])).
% 1.59/0.62  fof(f67,plain,(
% 1.59/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 1.59/0.62    inference(cnf_transformation,[],[f40])).
% 1.59/0.62  fof(f40,plain,(
% 1.59/0.62    ! [X0,X1,X2] : ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 1.59/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.59/0.62  fof(f39,plain,(
% 1.59/0.62    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) => (~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),X2)))),
% 1.59/0.62    introduced(choice_axiom,[])).
% 1.59/0.62  fof(f38,plain,(
% 1.59/0.62    ! [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,X0) & r2_hidden(X3,X1) & m1_subset_1(X3,X2)) | ~sP0(X0,X1,X2))),
% 1.59/0.62    inference(rectify,[],[f37])).
% 1.59/0.62  fof(f37,plain,(
% 1.59/0.62    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP0(X2,X1,X0))),
% 1.59/0.62    inference(nnf_transformation,[],[f29])).
% 1.59/0.64  fof(f29,plain,(
% 1.59/0.64    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~sP0(X2,X1,X0))),
% 1.59/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.64  fof(f157,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~r2_hidden(sK5(sK3,X0,X1),sK4) | ~sP0(sK3,X0,X1)) )),
% 1.59/0.64    inference(resolution,[],[f153,f68])).
% 1.59/0.64  fof(f68,plain,(
% 1.59/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f153,plain,(
% 1.59/0.64    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK4)) )),
% 1.59/0.64    inference(resolution,[],[f137,f111])).
% 1.59/0.64  fof(f111,plain,(
% 1.59/0.64    r2_hidden(sK4,k1_zfmisc_1(sK3))),
% 1.59/0.64    inference(subsumption_resolution,[],[f108,f52])).
% 1.59/0.64  fof(f52,plain,(
% 1.59/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.59/0.64    inference(cnf_transformation,[],[f17])).
% 1.59/0.64  fof(f17,axiom,(
% 1.59/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.59/0.64  fof(f108,plain,(
% 1.59/0.64    r2_hidden(sK4,k1_zfmisc_1(sK3)) | v1_xboole_0(k1_zfmisc_1(sK3))),
% 1.59/0.64    inference(resolution,[],[f61,f50])).
% 1.59/0.64  fof(f61,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f36])).
% 1.59/0.64  fof(f36,plain,(
% 1.59/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.59/0.64    inference(nnf_transformation,[],[f23])).
% 1.59/0.64  fof(f23,plain,(
% 1.59/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.59/0.64    inference(ennf_transformation,[],[f14])).
% 1.59/0.64  fof(f14,axiom,(
% 1.59/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.59/0.64  fof(f137,plain,(
% 1.59/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 1.59/0.64    inference(resolution,[],[f76,f132])).
% 1.59/0.64  fof(f132,plain,(
% 1.59/0.64    ( ! [X2,X3] : (~sP1(k1_zfmisc_1(X2),X3) | r2_hidden(X3,X2)) )),
% 1.59/0.64    inference(resolution,[],[f71,f96])).
% 1.59/0.64  fof(f96,plain,(
% 1.59/0.64    ( ! [X0] : (sP2(k1_zfmisc_1(X0),X0)) )),
% 1.59/0.64    inference(superposition,[],[f94,f54])).
% 1.59/0.64  fof(f54,plain,(
% 1.59/0.64    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.59/0.64    inference(cnf_transformation,[],[f13])).
% 1.59/0.64  fof(f13,axiom,(
% 1.59/0.64    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.59/0.64  fof(f94,plain,(
% 1.59/0.64    ( ! [X0] : (sP2(X0,k3_tarski(X0))) )),
% 1.59/0.64    inference(equality_resolution,[],[f77])).
% 1.59/0.64  fof(f77,plain,(
% 1.59/0.64    ( ! [X0,X1] : (sP2(X0,X1) | k3_tarski(X0) != X1) )),
% 1.59/0.64    inference(cnf_transformation,[],[f49])).
% 1.59/0.64  fof(f49,plain,(
% 1.59/0.64    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k3_tarski(X0) != X1))),
% 1.59/0.64    inference(nnf_transformation,[],[f33])).
% 1.59/0.64  fof(f33,plain,(
% 1.59/0.64    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP2(X0,X1))),
% 1.59/0.64    inference(definition_folding,[],[f11,f32,f31])).
% 1.59/0.64  fof(f31,plain,(
% 1.59/0.64    ! [X0,X2] : (sP1(X0,X2) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)))),
% 1.59/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.59/0.64  fof(f32,plain,(
% 1.59/0.64    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP1(X0,X2)))),
% 1.59/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.59/0.64  fof(f11,axiom,(
% 1.59/0.64    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.59/0.64  fof(f71,plain,(
% 1.59/0.64    ( ! [X0,X3,X1] : (~sP2(X0,X1) | ~sP1(X0,X3) | r2_hidden(X3,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f44])).
% 1.59/0.64  fof(f44,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP2(X0,X1) | ((~sP1(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP1(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP1(X0,X3)) & (sP1(X0,X3) | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 1.59/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 1.59/0.64  fof(f43,plain,(
% 1.59/0.64    ! [X1,X0] : (? [X2] : ((~sP1(X0,X2) | ~r2_hidden(X2,X1)) & (sP1(X0,X2) | r2_hidden(X2,X1))) => ((~sP1(X0,sK6(X0,X1)) | ~r2_hidden(sK6(X0,X1),X1)) & (sP1(X0,sK6(X0,X1)) | r2_hidden(sK6(X0,X1),X1))))),
% 1.59/0.64    introduced(choice_axiom,[])).
% 1.59/0.64  fof(f42,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((~sP1(X0,X2) | ~r2_hidden(X2,X1)) & (sP1(X0,X2) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP1(X0,X3)) & (sP1(X0,X3) | ~r2_hidden(X3,X1))) | ~sP2(X0,X1)))),
% 1.59/0.64    inference(rectify,[],[f41])).
% 1.59/0.64  fof(f41,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((~sP1(X0,X2) | ~r2_hidden(X2,X1)) & (sP1(X0,X2) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP1(X0,X2)) & (sP1(X0,X2) | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 1.59/0.64    inference(nnf_transformation,[],[f32])).
% 1.59/0.64  fof(f76,plain,(
% 1.59/0.64    ( ! [X2,X0,X1] : (sP1(X0,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X2)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f48])).
% 1.59/0.64  fof(f48,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP1(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & ((r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))) | ~sP1(X0,X1)))),
% 1.59/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).
% 1.59/0.64  fof(f47,plain,(
% 1.59/0.64    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) => (r2_hidden(sK7(X0,X1),X0) & r2_hidden(X1,sK7(X0,X1))))),
% 1.59/0.64    introduced(choice_axiom,[])).
% 1.59/0.64  fof(f46,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP1(X0,X1) | ! [X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X1,X2))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X1,X3)) | ~sP1(X0,X1)))),
% 1.59/0.64    inference(rectify,[],[f45])).
% 1.59/0.64  fof(f45,plain,(
% 1.59/0.64    ! [X0,X2] : ((sP1(X0,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~sP1(X0,X2)))),
% 1.59/0.64    inference(nnf_transformation,[],[f31])).
% 1.59/0.64  fof(f69,plain,(
% 1.59/0.64    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.64    inference(cnf_transformation,[],[f30])).
% 1.59/0.64  fof(f30,plain,(
% 1.59/0.64    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.64    inference(definition_folding,[],[f26,f29])).
% 1.59/0.64  fof(f26,plain,(
% 1.59/0.64    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.64    inference(flattening,[],[f25])).
% 1.59/0.64  fof(f25,plain,(
% 1.59/0.64    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.64    inference(ennf_transformation,[],[f19])).
% 1.59/0.64  fof(f19,axiom,(
% 1.59/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.59/0.64  % SZS output end Proof for theBenchmark
% 1.59/0.64  % (19403)------------------------------
% 1.59/0.64  % (19403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.64  % (19403)Termination reason: Refutation
% 1.59/0.64  
% 1.59/0.64  % (19403)Memory used [KB]: 6652
% 1.59/0.64  % (19403)Time elapsed: 0.197 s
% 1.59/0.64  % (19403)------------------------------
% 1.59/0.64  % (19403)------------------------------
% 1.59/0.64  % (19375)Success in time 0.265 s
%------------------------------------------------------------------------------
