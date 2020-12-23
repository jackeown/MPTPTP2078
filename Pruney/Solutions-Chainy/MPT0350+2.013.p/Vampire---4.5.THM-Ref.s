%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:51 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 268 expanded)
%              Number of leaves         :   41 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 ( 444 expanded)
%              Number of equality atoms :   98 ( 198 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f107,f118,f128,f175,f223,f318,f398,f561,f597,f655,f678,f714,f1013,f1033])).

fof(f1033,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) != k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | sK0 != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1013,plain,
    ( spl6_61
    | ~ spl6_2
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f999,f711,f93,f1010])).

fof(f1010,plain,
    ( spl6_61
  <=> k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f93,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f711,plain,
    ( spl6_44
  <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f999,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_44 ),
    inference(resolution,[],[f266,f713])).

fof(f713,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f711])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f83,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f714,plain,
    ( spl6_44
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f693,f675,f125,f711])).

fof(f125,plain,
    ( spl6_6
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f675,plain,
    ( spl6_39
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f693,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_39 ),
    inference(backward_demodulation,[],[f127,f677])).

fof(f677,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f675])).

fof(f127,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f678,plain,
    ( spl6_39
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f672,f638,f172,f675])).

fof(f172,plain,
    ( spl6_11
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f638,plain,
    ( spl6_37
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f672,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f174,f640])).

fof(f640,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f638])).

fof(f174,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f655,plain,
    ( spl6_37
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f636,f594,f638])).

fof(f594,plain,
    ( spl6_34
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f636,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl6_34 ),
    inference(superposition,[],[f45,f596])).

fof(f596,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f594])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f597,plain,
    ( spl6_34
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f592,f558,f594])).

fof(f558,plain,
    ( spl6_31
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f592,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl6_31 ),
    inference(resolution,[],[f560,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f560,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f558])).

fof(f561,plain,
    ( spl6_31
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f556,f104,f558])).

fof(f104,plain,
    ( spl6_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f556,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f550])).

fof(f550,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f539,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f539,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2),sK0)
        | r1_tarski(sK1,X2) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f530,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f530,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2),k3_tarski(k1_zfmisc_1(sK0)))
        | r1_tarski(sK1,X2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f143,f106])).

fof(f106,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f143,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(sK2(X1,X3),k3_tarski(X2))
      | r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f398,plain,
    ( spl6_24
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f386,f172,f395])).

fof(f395,plain,
    ( spl6_24
  <=> sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f386,plain,
    ( sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(superposition,[],[f371,f174])).

fof(f371,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f354,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f354,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f290,f162])).

fof(f162,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f67,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f290,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f159,f279])).

fof(f279,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f269,f43])).

fof(f269,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f159,f41])).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f67,f41])).

fof(f318,plain,
    ( spl6_21
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f313,f172,f315])).

fof(f315,plain,
    ( spl6_21
  <=> k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f313,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f312,f174])).

fof(f312,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f311,f45])).

fof(f311,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f310,f67])).

fof(f310,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))
    | ~ spl6_11 ),
    inference(forward_demodulation,[],[f298,f81])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f298,plain,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | ~ spl6_11 ),
    inference(superposition,[],[f80,f174])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f49,f78,f48,f78])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f223,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f102,f39])).

fof(f39,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f102,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f175,plain,
    ( spl6_11
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f168,f93,f172])).

fof(f168,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f95])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f128,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f123,f93,f125])).

fof(f123,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f95])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f118,plain,
    ( ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f113,f88,f115])).

fof(f115,plain,
    ( spl6_5
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f88,plain,
    ( spl6_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f113,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl6_1 ),
    inference(forward_demodulation,[],[f90,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f90,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f107,plain,
    ( spl6_3
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f98,f93,f104,f100])).

fof(f98,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f54,f95])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f96,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f91,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:57:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (17990)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (18014)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (17992)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (17991)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (18006)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (17997)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (17988)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (17998)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (18010)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (18013)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (18000)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (17989)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (18002)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18010)Refutation not found, incomplete strategy% (18010)------------------------------
% 0.22/0.54  % (18010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18010)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18010)Memory used [KB]: 10746
% 0.22/0.54  % (18010)Time elapsed: 0.096 s
% 0.22/0.54  % (18010)------------------------------
% 0.22/0.54  % (18010)------------------------------
% 0.22/0.54  % (17999)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (17994)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18015)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (17993)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (18017)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (18012)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (18016)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (17996)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (18011)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (18008)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18007)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (18004)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (18009)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (17995)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (18003)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (18001)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (18005)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (18005)Refutation not found, incomplete strategy% (18005)------------------------------
% 0.22/0.56  % (18005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18005)Memory used [KB]: 10618
% 0.22/0.56  % (18005)Time elapsed: 0.156 s
% 0.22/0.56  % (18005)------------------------------
% 0.22/0.56  % (18005)------------------------------
% 1.65/0.61  % (18004)Refutation found. Thanks to Tanya!
% 1.65/0.61  % SZS status Theorem for theBenchmark
% 1.65/0.61  % SZS output start Proof for theBenchmark
% 1.65/0.61  fof(f1034,plain,(
% 1.65/0.61    $false),
% 1.65/0.61    inference(avatar_sat_refutation,[],[f91,f96,f107,f118,f128,f175,f223,f318,f398,f561,f597,f655,f678,f714,f1013,f1033])).
% 1.65/0.61  fof(f1033,plain,(
% 1.65/0.61    sK1 != k3_xboole_0(sK0,sK1) | k3_subset_1(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) != k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | sK0 != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.65/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.65/0.61  fof(f1013,plain,(
% 1.65/0.61    spl6_61 | ~spl6_2 | ~spl6_44),
% 1.65/0.61    inference(avatar_split_clause,[],[f999,f711,f93,f1010])).
% 1.65/0.61  fof(f1010,plain,(
% 1.65/0.61    spl6_61 <=> k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 1.65/0.61  fof(f93,plain,(
% 1.65/0.61    spl6_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.65/0.61  fof(f711,plain,(
% 1.65/0.61    spl6_44 <=> m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.65/0.61  fof(f999,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | (~spl6_2 | ~spl6_44)),
% 1.65/0.61    inference(resolution,[],[f266,f713])).
% 1.65/0.61  fof(f713,plain,(
% 1.65/0.61    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_44),
% 1.65/0.61    inference(avatar_component_clause,[],[f711])).
% 1.65/0.61  fof(f266,plain,(
% 1.65/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ) | ~spl6_2),
% 1.65/0.61    inference(resolution,[],[f83,f95])).
% 1.65/0.61  fof(f95,plain,(
% 1.65/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.65/0.61    inference(avatar_component_clause,[],[f93])).
% 1.65/0.61  fof(f83,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f68,f78])).
% 1.65/0.61  fof(f78,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f47,f77])).
% 1.65/0.61  fof(f77,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f46,f76])).
% 1.65/0.61  fof(f76,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f66,f75])).
% 1.65/0.61  fof(f75,plain,(
% 1.65/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f69,f74])).
% 1.65/0.61  fof(f74,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f70,f73])).
% 1.65/0.61  fof(f73,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f71,f72])).
% 1.65/0.61  fof(f72,plain,(
% 1.65/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f16])).
% 1.65/0.61  fof(f16,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.65/0.61  fof(f71,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f15])).
% 1.65/0.61  fof(f15,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.65/0.61  fof(f70,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f14])).
% 1.65/0.61  fof(f14,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.65/0.61  fof(f69,plain,(
% 1.65/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f13])).
% 1.65/0.61  fof(f13,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.65/0.61  fof(f66,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f12])).
% 1.65/0.61  fof(f12,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.65/0.61  fof(f46,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f11])).
% 1.65/0.61  fof(f11,axiom,(
% 1.65/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.61  fof(f47,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f18])).
% 1.65/0.61  fof(f18,axiom,(
% 1.65/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.65/0.61  fof(f68,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f36])).
% 1.65/0.61  fof(f36,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(flattening,[],[f35])).
% 1.65/0.61  fof(f35,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.65/0.61    inference(ennf_transformation,[],[f25])).
% 1.65/0.61  fof(f25,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.65/0.61  fof(f714,plain,(
% 1.65/0.61    spl6_44 | ~spl6_6 | ~spl6_39),
% 1.65/0.61    inference(avatar_split_clause,[],[f693,f675,f125,f711])).
% 1.65/0.61  fof(f125,plain,(
% 1.65/0.61    spl6_6 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.65/0.61  fof(f675,plain,(
% 1.65/0.61    spl6_39 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.65/0.61  fof(f693,plain,(
% 1.65/0.61    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl6_6 | ~spl6_39)),
% 1.65/0.61    inference(backward_demodulation,[],[f127,f677])).
% 1.65/0.61  fof(f677,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl6_39),
% 1.65/0.61    inference(avatar_component_clause,[],[f675])).
% 1.65/0.61  fof(f127,plain,(
% 1.65/0.61    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_6),
% 1.65/0.61    inference(avatar_component_clause,[],[f125])).
% 1.65/0.61  fof(f678,plain,(
% 1.65/0.61    spl6_39 | ~spl6_11 | ~spl6_37),
% 1.65/0.61    inference(avatar_split_clause,[],[f672,f638,f172,f675])).
% 1.65/0.61  fof(f172,plain,(
% 1.65/0.61    spl6_11 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.65/0.61  fof(f638,plain,(
% 1.65/0.61    spl6_37 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.65/0.61  fof(f672,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | (~spl6_11 | ~spl6_37)),
% 1.65/0.61    inference(backward_demodulation,[],[f174,f640])).
% 1.65/0.61  fof(f640,plain,(
% 1.65/0.61    sK1 = k3_xboole_0(sK0,sK1) | ~spl6_37),
% 1.65/0.61    inference(avatar_component_clause,[],[f638])).
% 1.65/0.61  fof(f174,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl6_11),
% 1.65/0.61    inference(avatar_component_clause,[],[f172])).
% 1.65/0.61  fof(f655,plain,(
% 1.65/0.61    spl6_37 | ~spl6_34),
% 1.65/0.61    inference(avatar_split_clause,[],[f636,f594,f638])).
% 1.65/0.61  fof(f594,plain,(
% 1.65/0.61    spl6_34 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.65/0.61  fof(f636,plain,(
% 1.65/0.61    sK1 = k3_xboole_0(sK0,sK1) | ~spl6_34),
% 1.65/0.61    inference(superposition,[],[f45,f596])).
% 1.65/0.61  fof(f596,plain,(
% 1.65/0.61    sK1 = k3_xboole_0(sK1,sK0) | ~spl6_34),
% 1.65/0.61    inference(avatar_component_clause,[],[f594])).
% 1.65/0.61  fof(f45,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f1])).
% 1.65/0.61  fof(f1,axiom,(
% 1.65/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.65/0.61  fof(f597,plain,(
% 1.65/0.61    spl6_34 | ~spl6_31),
% 1.65/0.61    inference(avatar_split_clause,[],[f592,f558,f594])).
% 1.65/0.61  fof(f558,plain,(
% 1.65/0.61    spl6_31 <=> r1_tarski(sK1,sK0)),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.65/0.61  fof(f592,plain,(
% 1.65/0.61    sK1 = k3_xboole_0(sK1,sK0) | ~spl6_31),
% 1.65/0.61    inference(resolution,[],[f560,f55])).
% 1.65/0.61  fof(f55,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.65/0.61    inference(cnf_transformation,[],[f31])).
% 1.65/0.61  fof(f31,plain,(
% 1.65/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.65/0.61    inference(ennf_transformation,[],[f4])).
% 1.65/0.61  fof(f4,axiom,(
% 1.65/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.65/0.61  fof(f560,plain,(
% 1.65/0.61    r1_tarski(sK1,sK0) | ~spl6_31),
% 1.65/0.61    inference(avatar_component_clause,[],[f558])).
% 1.65/0.61  fof(f561,plain,(
% 1.65/0.61    spl6_31 | ~spl6_4),
% 1.65/0.61    inference(avatar_split_clause,[],[f556,f104,f558])).
% 1.65/0.61  fof(f104,plain,(
% 1.65/0.61    spl6_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.65/0.61  fof(f556,plain,(
% 1.65/0.61    r1_tarski(sK1,sK0) | ~spl6_4),
% 1.65/0.61    inference(duplicate_literal_removal,[],[f550])).
% 1.65/0.61  fof(f550,plain,(
% 1.65/0.61    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl6_4),
% 1.65/0.61    inference(resolution,[],[f539,f59])).
% 1.65/0.61  fof(f59,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f34])).
% 1.65/0.61  fof(f34,plain,(
% 1.65/0.61    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f28])).
% 1.65/0.61  fof(f28,plain,(
% 1.65/0.61    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.65/0.61    inference(unused_predicate_definition_removal,[],[f2])).
% 1.65/0.61  fof(f2,axiom,(
% 1.65/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.65/0.61  fof(f539,plain,(
% 1.65/0.61    ( ! [X2] : (r2_hidden(sK2(sK1,X2),sK0) | r1_tarski(sK1,X2)) ) | ~spl6_4),
% 1.65/0.61    inference(forward_demodulation,[],[f530,f42])).
% 1.65/0.61  fof(f42,plain,(
% 1.65/0.61    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.65/0.61    inference(cnf_transformation,[],[f19])).
% 1.65/0.61  fof(f19,axiom,(
% 1.65/0.61    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.65/0.61  fof(f530,plain,(
% 1.65/0.61    ( ! [X2] : (r2_hidden(sK2(sK1,X2),k3_tarski(k1_zfmisc_1(sK0))) | r1_tarski(sK1,X2)) ) | ~spl6_4),
% 1.65/0.61    inference(resolution,[],[f143,f106])).
% 1.65/0.61  fof(f106,plain,(
% 1.65/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl6_4),
% 1.65/0.61    inference(avatar_component_clause,[],[f104])).
% 1.65/0.61  fof(f143,plain,(
% 1.65/0.61    ( ! [X2,X3,X1] : (~r2_hidden(X1,X2) | r2_hidden(sK2(X1,X3),k3_tarski(X2)) | r1_tarski(X1,X3)) )),
% 1.65/0.61    inference(resolution,[],[f84,f58])).
% 1.65/0.61  fof(f58,plain,(
% 1.65/0.61    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f34])).
% 1.65/0.61  fof(f84,plain,(
% 1.65/0.61    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 1.65/0.61    inference(equality_resolution,[],[f65])).
% 1.65/0.61  fof(f65,plain,(
% 1.65/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.65/0.61    inference(cnf_transformation,[],[f17])).
% 1.65/0.61  fof(f17,axiom,(
% 1.65/0.61    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.65/0.61  fof(f398,plain,(
% 1.65/0.61    spl6_24 | ~spl6_11),
% 1.65/0.61    inference(avatar_split_clause,[],[f386,f172,f395])).
% 1.65/0.61  fof(f395,plain,(
% 1.65/0.61    spl6_24 <=> sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.65/0.61  fof(f386,plain,(
% 1.65/0.61    sK0 = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)) | ~spl6_11),
% 1.65/0.61    inference(superposition,[],[f371,f174])).
% 1.65/0.61  fof(f371,plain,(
% 1.65/0.61    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.65/0.61    inference(forward_demodulation,[],[f354,f43])).
% 1.65/0.61  fof(f43,plain,(
% 1.65/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/0.61    inference(cnf_transformation,[],[f6])).
% 1.65/0.61  fof(f6,axiom,(
% 1.65/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.65/0.61  fof(f354,plain,(
% 1.65/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.65/0.61    inference(superposition,[],[f290,f162])).
% 1.65/0.61  fof(f162,plain,(
% 1.65/0.61    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.65/0.61    inference(superposition,[],[f67,f41])).
% 1.65/0.61  fof(f41,plain,(
% 1.65/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f8])).
% 1.65/0.61  fof(f8,axiom,(
% 1.65/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.65/0.61  fof(f67,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f7])).
% 1.65/0.61  fof(f7,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.65/0.61  fof(f290,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.65/0.61    inference(backward_demodulation,[],[f159,f279])).
% 1.65/0.61  fof(f279,plain,(
% 1.65/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.65/0.61    inference(forward_demodulation,[],[f269,f43])).
% 1.65/0.61  fof(f269,plain,(
% 1.65/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.65/0.61    inference(superposition,[],[f159,f41])).
% 1.65/0.61  fof(f159,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.65/0.61    inference(superposition,[],[f67,f41])).
% 1.65/0.61  fof(f318,plain,(
% 1.65/0.61    spl6_21 | ~spl6_11),
% 1.65/0.61    inference(avatar_split_clause,[],[f313,f172,f315])).
% 1.65/0.61  fof(f315,plain,(
% 1.65/0.61    spl6_21 <=> k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.65/0.61  fof(f313,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl6_11),
% 1.65/0.61    inference(forward_demodulation,[],[f312,f174])).
% 1.65/0.61  fof(f312,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | ~spl6_11),
% 1.65/0.61    inference(forward_demodulation,[],[f311,f45])).
% 1.65/0.61  fof(f311,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,sK0))) | ~spl6_11),
% 1.65/0.61    inference(forward_demodulation,[],[f310,f67])).
% 1.65/0.61  fof(f310,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) = k5_xboole_0(k5_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)) | ~spl6_11),
% 1.65/0.61    inference(forward_demodulation,[],[f298,f81])).
% 1.65/0.61  fof(f81,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f50,f78])).
% 1.65/0.61  fof(f50,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f9])).
% 1.65/0.61  fof(f9,axiom,(
% 1.65/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.65/0.61  fof(f298,plain,(
% 1.65/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | ~spl6_11),
% 1.65/0.61    inference(superposition,[],[f80,f174])).
% 1.65/0.61  fof(f80,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f49,f78,f48,f78])).
% 1.65/0.61  fof(f48,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f3])).
% 1.65/0.61  fof(f3,axiom,(
% 1.65/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.61  fof(f49,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f5])).
% 1.65/0.61  fof(f5,axiom,(
% 1.65/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.65/0.61  fof(f223,plain,(
% 1.65/0.61    ~spl6_3),
% 1.65/0.61    inference(avatar_contradiction_clause,[],[f221])).
% 1.65/0.61  fof(f221,plain,(
% 1.65/0.61    $false | ~spl6_3),
% 1.65/0.61    inference(resolution,[],[f102,f39])).
% 1.65/0.61  fof(f39,plain,(
% 1.65/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f24])).
% 1.65/0.61  fof(f24,axiom,(
% 1.65/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.65/0.61  fof(f102,plain,(
% 1.65/0.61    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_3),
% 1.65/0.61    inference(avatar_component_clause,[],[f100])).
% 1.65/0.61  fof(f100,plain,(
% 1.65/0.61    spl6_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.65/0.61  fof(f175,plain,(
% 1.65/0.61    spl6_11 | ~spl6_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f168,f93,f172])).
% 1.65/0.61  fof(f168,plain,(
% 1.65/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 1.65/0.61    inference(resolution,[],[f82,f95])).
% 1.65/0.61  fof(f82,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.65/0.61    inference(definition_unfolding,[],[f57,f48])).
% 1.65/0.61  fof(f57,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f33])).
% 1.65/0.61  fof(f33,plain,(
% 1.65/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f22])).
% 1.65/0.61  fof(f22,axiom,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.61  fof(f128,plain,(
% 1.65/0.61    spl6_6 | ~spl6_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f123,f93,f125])).
% 1.65/0.61  fof(f123,plain,(
% 1.65/0.61    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.65/0.61    inference(resolution,[],[f56,f95])).
% 1.65/0.61  fof(f56,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f32])).
% 1.65/0.61  fof(f32,plain,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f23])).
% 1.65/0.61  fof(f23,axiom,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.65/0.61  fof(f118,plain,(
% 1.65/0.61    ~spl6_5 | spl6_1),
% 1.65/0.61    inference(avatar_split_clause,[],[f113,f88,f115])).
% 1.65/0.61  fof(f115,plain,(
% 1.65/0.61    spl6_5 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.65/0.61  fof(f88,plain,(
% 1.65/0.61    spl6_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.65/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.65/0.61  fof(f113,plain,(
% 1.65/0.61    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl6_1),
% 1.65/0.61    inference(forward_demodulation,[],[f90,f40])).
% 1.65/0.61  fof(f40,plain,(
% 1.65/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.65/0.61    inference(cnf_transformation,[],[f21])).
% 1.65/0.61  fof(f21,axiom,(
% 1.65/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.65/0.61  fof(f90,plain,(
% 1.65/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl6_1),
% 1.65/0.61    inference(avatar_component_clause,[],[f88])).
% 1.65/0.61  fof(f107,plain,(
% 1.65/0.61    spl6_3 | spl6_4 | ~spl6_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f98,f93,f104,f100])).
% 1.65/0.61  fof(f98,plain,(
% 1.65/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl6_2),
% 1.65/0.61    inference(resolution,[],[f54,f95])).
% 1.65/0.61  fof(f54,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f30])).
% 1.65/0.61  fof(f30,plain,(
% 1.65/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f20])).
% 1.65/0.61  fof(f20,axiom,(
% 1.65/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.65/0.61  fof(f96,plain,(
% 1.65/0.61    spl6_2),
% 1.65/0.61    inference(avatar_split_clause,[],[f37,f93])).
% 1.65/0.61  fof(f37,plain,(
% 1.65/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.61    inference(cnf_transformation,[],[f29])).
% 1.65/0.61  fof(f29,plain,(
% 1.65/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f27])).
% 1.65/0.61  fof(f27,negated_conjecture,(
% 1.65/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.65/0.61    inference(negated_conjecture,[],[f26])).
% 1.65/0.61  fof(f26,conjecture,(
% 1.65/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.65/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.65/0.61  fof(f91,plain,(
% 1.65/0.61    ~spl6_1),
% 1.65/0.61    inference(avatar_split_clause,[],[f38,f88])).
% 1.65/0.61  fof(f38,plain,(
% 1.65/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.65/0.61    inference(cnf_transformation,[],[f29])).
% 1.65/0.61  % SZS output end Proof for theBenchmark
% 1.65/0.61  % (18004)------------------------------
% 1.65/0.61  % (18004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (18004)Termination reason: Refutation
% 1.65/0.61  
% 1.65/0.61  % (18004)Memory used [KB]: 11641
% 1.65/0.61  % (18004)Time elapsed: 0.202 s
% 1.65/0.61  % (18004)------------------------------
% 1.65/0.61  % (18004)------------------------------
% 1.65/0.61  % (17984)Success in time 0.248 s
%------------------------------------------------------------------------------
