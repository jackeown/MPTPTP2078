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
% DateTime   : Thu Dec  3 12:43:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 284 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 397 expanded)
%              Number of equality atoms :   70 ( 250 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f71,f76,f149,f297])).

fof(f297,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f295,f70])).

fof(f70,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f295,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f118,f293])).

fof(f293,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f190,f292])).

fof(f292,plain,(
    ! [X8,X9] : k3_tarski(k2_enumset1(X8,X8,X8,k4_xboole_0(X8,X9))) = X8 ),
    inference(forward_demodulation,[],[f286,f43])).

fof(f43,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f286,plain,(
    ! [X8,X9] : k3_tarski(k2_enumset1(X8,X8,X8,k4_xboole_0(X8,X9))) = k3_tarski(k2_enumset1(X8,X8,X8,k1_xboole_0)) ),
    inference(superposition,[],[f46,f181])).

fof(f181,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f83,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f83,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(superposition,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f41,f41])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f44,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f42,f42])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f190,plain,
    ( k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f189,f45])).

fof(f189,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f188,f46])).

fof(f188,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f187,f45])).

fof(f187,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f186,f45])).

fof(f186,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0))
    | ~ spl2_8 ),
    inference(superposition,[],[f46,f148])).

fof(f148,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_8
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f118,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f117,f45])).

fof(f117,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f112,f46])).

fof(f112,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f53,f75,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f75,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f149,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f99,f73,f51,f146])).

fof(f99,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f94,f80])).

fof(f80,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f77,f62])).

fof(f62,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f77,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f94,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f75,f36])).

fof(f76,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f65,f51,f73])).

fof(f65,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f60,f62])).

fof(f60,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f71,plain,
    ( ~ spl2_3
    | ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f66,f56,f51,f68])).

fof(f56,plain,
    ( spl2_2
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_1
    | spl2_2 ),
    inference(backward_demodulation,[],[f58,f62])).

fof(f58,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f49,f56])).

fof(f49,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f27,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f26,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f54,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:02:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.23/0.48  % (7585)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.48  % (7583)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.48  % (7595)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.48  % (7596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.49  % (7587)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.49  % (7592)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.49  % (7581)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.49  % (7596)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f298,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(avatar_sat_refutation,[],[f54,f59,f71,f76,f149,f297])).
% 0.23/0.49  fof(f297,plain,(
% 0.23/0.49    ~spl2_1 | spl2_3 | ~spl2_4 | ~spl2_8),
% 0.23/0.49    inference(avatar_contradiction_clause,[],[f296])).
% 0.23/0.50  fof(f296,plain,(
% 0.23/0.50    $false | (~spl2_1 | spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.23/0.50    inference(subsumption_resolution,[],[f295,f70])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | spl2_3),
% 0.23/0.50    inference(avatar_component_clause,[],[f68])).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.50  fof(f295,plain,(
% 0.23/0.50    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_8)),
% 0.23/0.50    inference(backward_demodulation,[],[f118,f293])).
% 0.23/0.50  fof(f293,plain,(
% 0.23/0.50    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl2_8),
% 0.23/0.50    inference(backward_demodulation,[],[f190,f292])).
% 0.23/0.50  fof(f292,plain,(
% 0.23/0.50    ( ! [X8,X9] : (k3_tarski(k2_enumset1(X8,X8,X8,k4_xboole_0(X8,X9))) = X8) )),
% 0.23/0.50    inference(forward_demodulation,[],[f286,f43])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.23/0.50    inference(definition_unfolding,[],[f28,f42])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f33,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f32,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.50  fof(f286,plain,(
% 0.23/0.50    ( ! [X8,X9] : (k3_tarski(k2_enumset1(X8,X8,X8,k4_xboole_0(X8,X9))) = k3_tarski(k2_enumset1(X8,X8,X8,k1_xboole_0))) )),
% 0.23/0.50    inference(superposition,[],[f46,f181])).
% 0.23/0.50  fof(f181,plain,(
% 0.23/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 0.23/0.50    inference(superposition,[],[f83,f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f39,f42])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))) )),
% 0.23/0.50    inference(superposition,[],[f44,f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f31,f41,f41])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f30,f42])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f34,f42,f42])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.50  fof(f190,plain,(
% 0.23/0.50    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl2_8),
% 0.23/0.50    inference(forward_demodulation,[],[f189,f45])).
% 0.23/0.50  fof(f189,plain,(
% 0.23/0.50    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl2_8),
% 0.23/0.50    inference(forward_demodulation,[],[f188,f46])).
% 0.23/0.50  fof(f188,plain,(
% 0.23/0.50    k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl2_8),
% 0.23/0.50    inference(forward_demodulation,[],[f187,f45])).
% 0.23/0.50  fof(f187,plain,(
% 0.23/0.50    k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl2_8),
% 0.23/0.50    inference(forward_demodulation,[],[f186,f45])).
% 0.23/0.50  fof(f186,plain,(
% 0.23/0.50    k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) | ~spl2_8),
% 0.23/0.50    inference(superposition,[],[f46,f148])).
% 0.23/0.50  fof(f148,plain,(
% 0.23/0.50    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_8),
% 0.23/0.50    inference(avatar_component_clause,[],[f146])).
% 0.23/0.50  fof(f146,plain,(
% 0.23/0.50    spl2_8 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.50  fof(f118,plain,(
% 0.23/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | (~spl2_1 | ~spl2_4)),
% 0.23/0.50    inference(forward_demodulation,[],[f117,f45])).
% 0.23/0.50  fof(f117,plain,(
% 0.23/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | (~spl2_1 | ~spl2_4)),
% 0.23/0.50    inference(forward_demodulation,[],[f112,f46])).
% 0.23/0.50  fof(f112,plain,(
% 0.23/0.50    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_4)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f53,f75,f48])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(definition_unfolding,[],[f40,f42])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(flattening,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.23/0.50    inference(ennf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.23/0.50    inference(avatar_component_clause,[],[f73])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    spl2_4 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f51])).
% 0.23/0.50  fof(f51,plain,(
% 0.23/0.50    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.50  fof(f149,plain,(
% 0.23/0.50    spl2_8 | ~spl2_1 | ~spl2_4),
% 0.23/0.50    inference(avatar_split_clause,[],[f99,f73,f51,f146])).
% 0.23/0.50  fof(f99,plain,(
% 0.23/0.50    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_4)),
% 0.23/0.50    inference(forward_demodulation,[],[f94,f80])).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_1),
% 0.23/0.50    inference(forward_demodulation,[],[f77,f62])).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_1),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f53,f36])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f53,f37])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f13])).
% 0.23/0.50  fof(f13,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_4),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f75,f36])).
% 0.23/0.50  fof(f76,plain,(
% 0.23/0.50    spl2_4 | ~spl2_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f65,f51,f73])).
% 0.23/0.50  fof(f65,plain,(
% 0.23/0.50    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.23/0.50    inference(backward_demodulation,[],[f60,f62])).
% 0.23/0.50  fof(f60,plain,(
% 0.23/0.50    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f53,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    ~spl2_3 | ~spl2_1 | spl2_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f66,f56,f51,f68])).
% 0.23/0.50  fof(f56,plain,(
% 0.23/0.50    spl2_2 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.50  fof(f66,plain,(
% 0.23/0.50    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (~spl2_1 | spl2_2)),
% 0.23/0.50    inference(backward_demodulation,[],[f58,f62])).
% 0.23/0.50  fof(f58,plain,(
% 0.23/0.50    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f56])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ~spl2_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f49,f56])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.23/0.50    inference(backward_demodulation,[],[f26,f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,axiom,(
% 0.23/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.23/0.50    inference(cnf_transformation,[],[f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.23/0.50    inference(negated_conjecture,[],[f15])).
% 0.23/0.50  fof(f15,conjecture,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    spl2_1),
% 0.23/0.50    inference(avatar_split_clause,[],[f25,f51])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.50    inference(cnf_transformation,[],[f24])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (7596)------------------------------
% 0.23/0.50  % (7596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (7596)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (7596)Memory used [KB]: 10874
% 0.23/0.50  % (7596)Time elapsed: 0.015 s
% 0.23/0.50  % (7596)------------------------------
% 0.23/0.50  % (7596)------------------------------
% 0.23/0.50  % (7584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (7594)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.50  % (7580)Success in time 0.12 s
%------------------------------------------------------------------------------
