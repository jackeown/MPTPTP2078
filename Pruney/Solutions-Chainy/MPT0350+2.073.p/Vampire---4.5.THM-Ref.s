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
% DateTime   : Thu Dec  3 12:44:01 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 169 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 ( 348 expanded)
%              Number of equality atoms :   59 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f936,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f92,f110,f147,f153,f194,f200,f205,f239,f281,f840,f869,f885,f929])).

fof(f929,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f928,f882,f278,f78,f150])).

fof(f150,plain,
    ( spl5_9
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f78,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f278,plain,
    ( spl5_16
  <=> sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f882,plain,
    ( spl5_49
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f928,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_16
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f923,f280])).

fof(f280,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f278])).

fof(f923,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_49 ),
    inference(resolution,[],[f884,f259])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f60,f80])).

fof(f80,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f884,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f882])).

fof(f885,plain,
    ( spl5_49
    | spl5_3
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f874,f866,f85,f882])).

fof(f85,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f866,plain,
    ( spl5_47
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f874,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_47 ),
    inference(resolution,[],[f868,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f868,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f866])).

fof(f869,plain,
    ( spl5_47
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f859,f837,f866])).

fof(f837,plain,
    ( spl5_45
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f859,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_45 ),
    inference(resolution,[],[f839,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f839,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f837])).

fof(f840,plain,
    ( spl5_45
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f829,f185,f837])).

fof(f185,plain,
    ( spl5_12
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f829,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_12 ),
    inference(superposition,[],[f706,f187])).

fof(f187,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f706,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(duplicate_literal_removal,[],[f681])).

fof(f681,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ) ),
    inference(resolution,[],[f135,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ) ),
    inference(resolution,[],[f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f281,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f269,f185,f278])).

fof(f269,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl5_12 ),
    inference(superposition,[],[f58,f187])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f55,f33])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f239,plain,
    ( spl5_12
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f229,f125,f185])).

fof(f125,plain,
    ( spl5_7
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f229,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f57,f127])).

fof(f127,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f33,f33])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f205,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f203,f96,f125])).

fof(f96,plain,
    ( spl5_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f203,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f98,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f98,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f200,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f93,f89,f96])).

fof(f89,plain,
    ( spl5_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f194,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f87,f27])).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f87,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f153,plain,
    ( ~ spl5_9
    | spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f148,f144,f107,f150])).

fof(f107,plain,
    ( spl5_6
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f144,plain,
    ( spl5_8
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f148,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl5_6
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f109,f146])).

fof(f146,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f109,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f147,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f141,f78,f144])).

fof(f141,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f40,f80])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f110,plain,
    ( ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f105,f73,f107])).

fof(f73,plain,
    ( spl5_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f105,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f75,f28])).

fof(f28,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f75,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f92,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f83,f78,f89,f85])).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f80])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f78])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f73])).

fof(f26,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (13869)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (13885)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (13865)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (13886)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (13867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (13878)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (13876)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13870)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13888)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (13885)Refutation not found, incomplete strategy% (13885)------------------------------
% 0.20/0.53  % (13885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13885)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13885)Memory used [KB]: 10746
% 0.20/0.53  % (13885)Time elapsed: 0.116 s
% 0.20/0.53  % (13885)------------------------------
% 0.20/0.53  % (13885)------------------------------
% 0.20/0.53  % (13873)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (13881)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (13887)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (13877)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (13873)Refutation not found, incomplete strategy% (13873)------------------------------
% 0.20/0.53  % (13873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13873)Memory used [KB]: 10618
% 0.20/0.53  % (13873)Time elapsed: 0.128 s
% 0.20/0.53  % (13873)------------------------------
% 0.20/0.53  % (13873)------------------------------
% 0.20/0.53  % (13864)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (13884)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (13891)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (13866)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (13868)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (13880)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (13880)Refutation not found, incomplete strategy% (13880)------------------------------
% 0.20/0.54  % (13880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13880)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13880)Memory used [KB]: 10618
% 0.20/0.54  % (13880)Time elapsed: 0.128 s
% 0.20/0.54  % (13880)------------------------------
% 0.20/0.54  % (13880)------------------------------
% 0.20/0.54  % (13872)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (13879)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (13872)Refutation not found, incomplete strategy% (13872)------------------------------
% 0.20/0.54  % (13872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13872)Memory used [KB]: 10618
% 0.20/0.54  % (13872)Time elapsed: 0.138 s
% 0.20/0.54  % (13872)------------------------------
% 0.20/0.54  % (13872)------------------------------
% 0.20/0.54  % (13892)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (13863)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (13863)Refutation not found, incomplete strategy% (13863)------------------------------
% 0.20/0.54  % (13863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13863)Memory used [KB]: 1663
% 0.20/0.54  % (13863)Time elapsed: 0.139 s
% 0.20/0.54  % (13863)------------------------------
% 0.20/0.54  % (13863)------------------------------
% 0.20/0.54  % (13882)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (13889)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (13890)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (13871)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (13883)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (13874)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (13874)Refutation not found, incomplete strategy% (13874)------------------------------
% 0.20/0.55  % (13874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13874)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13874)Memory used [KB]: 10618
% 0.20/0.55  % (13874)Time elapsed: 0.150 s
% 0.20/0.55  % (13874)------------------------------
% 0.20/0.55  % (13874)------------------------------
% 0.20/0.56  % (13875)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.79/0.60  % (13879)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f936,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(avatar_sat_refutation,[],[f76,f81,f92,f110,f147,f153,f194,f200,f205,f239,f281,f840,f869,f885,f929])).
% 1.79/0.60  fof(f929,plain,(
% 1.79/0.60    spl5_9 | ~spl5_2 | ~spl5_16 | ~spl5_49),
% 1.79/0.60    inference(avatar_split_clause,[],[f928,f882,f278,f78,f150])).
% 1.79/0.60  fof(f150,plain,(
% 1.79/0.60    spl5_9 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.79/0.60  fof(f278,plain,(
% 1.79/0.60    spl5_16 <=> sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.79/0.60  fof(f882,plain,(
% 1.79/0.60    spl5_49 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.79/0.60  fof(f928,plain,(
% 1.79/0.60    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_16 | ~spl5_49)),
% 1.79/0.60    inference(forward_demodulation,[],[f923,f280])).
% 1.79/0.60  fof(f280,plain,(
% 1.79/0.60    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | ~spl5_16),
% 1.79/0.60    inference(avatar_component_clause,[],[f278])).
% 1.79/0.60  fof(f923,plain,(
% 1.79/0.60    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | (~spl5_2 | ~spl5_49)),
% 1.79/0.60    inference(resolution,[],[f884,f259])).
% 1.79/0.60  fof(f259,plain,(
% 1.79/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0))) ) | ~spl5_2),
% 1.79/0.60    inference(resolution,[],[f60,f80])).
% 1.79/0.60  fof(f80,plain,(
% 1.79/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.79/0.60    inference(avatar_component_clause,[],[f78])).
% 1.79/0.60  fof(f60,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f48,f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f30,f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f10])).
% 1.79/0.60  fof(f10,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.79/0.60  fof(f48,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f24])).
% 1.79/0.60  fof(f24,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(flattening,[],[f23])).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.79/0.60    inference(ennf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.79/0.60  fof(f884,plain,(
% 1.79/0.60    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_49),
% 1.79/0.60    inference(avatar_component_clause,[],[f882])).
% 1.79/0.60  fof(f885,plain,(
% 1.79/0.60    spl5_49 | spl5_3 | ~spl5_47),
% 1.79/0.60    inference(avatar_split_clause,[],[f874,f866,f85,f882])).
% 1.79/0.60  fof(f85,plain,(
% 1.79/0.60    spl5_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.79/0.60  fof(f866,plain,(
% 1.79/0.60    spl5_47 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.79/0.60  fof(f874,plain,(
% 1.79/0.60    v1_xboole_0(k1_zfmisc_1(sK0)) | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_47),
% 1.79/0.60    inference(resolution,[],[f868,f37])).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f19,plain,(
% 1.79/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f11])).
% 1.79/0.60  fof(f11,axiom,(
% 1.79/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.79/0.60  fof(f868,plain,(
% 1.79/0.60    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_47),
% 1.79/0.60    inference(avatar_component_clause,[],[f866])).
% 1.79/0.60  fof(f869,plain,(
% 1.79/0.60    spl5_47 | ~spl5_45),
% 1.79/0.60    inference(avatar_split_clause,[],[f859,f837,f866])).
% 1.79/0.60  fof(f837,plain,(
% 1.79/0.60    spl5_45 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.79/0.60  fof(f859,plain,(
% 1.79/0.60    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_45),
% 1.79/0.60    inference(resolution,[],[f839,f68])).
% 1.79/0.60  fof(f68,plain,(
% 1.79/0.60    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(equality_resolution,[],[f44])).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.79/0.60  fof(f839,plain,(
% 1.79/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl5_45),
% 1.79/0.60    inference(avatar_component_clause,[],[f837])).
% 1.79/0.60  fof(f840,plain,(
% 1.79/0.60    spl5_45 | ~spl5_12),
% 1.79/0.60    inference(avatar_split_clause,[],[f829,f185,f837])).
% 1.79/0.60  fof(f185,plain,(
% 1.79/0.60    spl5_12 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.79/0.60  fof(f829,plain,(
% 1.79/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl5_12),
% 1.79/0.60    inference(superposition,[],[f706,f187])).
% 1.79/0.60  fof(f187,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_12),
% 1.79/0.60    inference(avatar_component_clause,[],[f185])).
% 1.79/0.60  fof(f706,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f681])).
% 1.79/0.60  fof(f681,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.79/0.60    inference(resolution,[],[f135,f43])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f22])).
% 1.79/0.60  fof(f22,plain,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.79/0.60  fof(f135,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X0) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.79/0.60    inference(resolution,[],[f71,f42])).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f22])).
% 1.79/0.60  fof(f71,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f63])).
% 1.79/0.60  fof(f63,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.79/0.60    inference(definition_unfolding,[],[f52,f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.79/0.60  fof(f281,plain,(
% 1.79/0.60    spl5_16 | ~spl5_12),
% 1.79/0.60    inference(avatar_split_clause,[],[f269,f185,f278])).
% 1.79/0.60  fof(f269,plain,(
% 1.79/0.60    sK0 = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | ~spl5_12),
% 1.79/0.60    inference(superposition,[],[f58,f187])).
% 1.79/0.60  fof(f58,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f34,f55,f33])).
% 1.79/0.60  fof(f34,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.79/0.60  fof(f239,plain,(
% 1.79/0.60    spl5_12 | ~spl5_7),
% 1.79/0.60    inference(avatar_split_clause,[],[f229,f125,f185])).
% 1.79/0.60  fof(f125,plain,(
% 1.79/0.60    spl5_7 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.79/0.60  fof(f229,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_7),
% 1.79/0.60    inference(superposition,[],[f57,f127])).
% 1.79/0.60  fof(f127,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl5_7),
% 1.79/0.60    inference(avatar_component_clause,[],[f125])).
% 1.79/0.60  fof(f57,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f29,f33,f33])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.60  fof(f205,plain,(
% 1.79/0.60    spl5_7 | ~spl5_5),
% 1.79/0.60    inference(avatar_split_clause,[],[f203,f96,f125])).
% 1.79/0.60  fof(f96,plain,(
% 1.79/0.60    spl5_5 <=> r1_tarski(sK1,sK0)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.79/0.60  fof(f203,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl5_5),
% 1.79/0.60    inference(resolution,[],[f98,f59])).
% 1.79/0.60  fof(f59,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.79/0.60    inference(definition_unfolding,[],[f39,f33])).
% 1.79/0.60  fof(f39,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.79/0.60  fof(f98,plain,(
% 1.79/0.60    r1_tarski(sK1,sK0) | ~spl5_5),
% 1.79/0.60    inference(avatar_component_clause,[],[f96])).
% 1.79/0.60  fof(f200,plain,(
% 1.79/0.60    spl5_5 | ~spl5_4),
% 1.79/0.60    inference(avatar_split_clause,[],[f93,f89,f96])).
% 1.79/0.60  fof(f89,plain,(
% 1.79/0.60    spl5_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.79/0.60  fof(f93,plain,(
% 1.79/0.60    r1_tarski(sK1,sK0) | ~spl5_4),
% 1.79/0.60    inference(resolution,[],[f91,f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f45])).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f9])).
% 1.79/0.60  fof(f91,plain,(
% 1.79/0.60    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.79/0.60    inference(avatar_component_clause,[],[f89])).
% 1.79/0.60  fof(f194,plain,(
% 1.79/0.60    ~spl5_3),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f192])).
% 1.79/0.60  fof(f192,plain,(
% 1.79/0.60    $false | ~spl5_3),
% 1.79/0.60    inference(resolution,[],[f87,f27])).
% 1.79/0.60  fof(f27,plain,(
% 1.79/0.60    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f14])).
% 1.79/0.60  fof(f14,axiom,(
% 1.79/0.60    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.79/0.60  fof(f87,plain,(
% 1.79/0.60    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_3),
% 1.79/0.60    inference(avatar_component_clause,[],[f85])).
% 1.79/0.60  fof(f153,plain,(
% 1.79/0.60    ~spl5_9 | spl5_6 | ~spl5_8),
% 1.79/0.60    inference(avatar_split_clause,[],[f148,f144,f107,f150])).
% 1.79/0.60  fof(f107,plain,(
% 1.79/0.60    spl5_6 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.79/0.60  fof(f144,plain,(
% 1.79/0.60    spl5_8 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.79/0.60  fof(f148,plain,(
% 1.79/0.60    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (spl5_6 | ~spl5_8)),
% 1.79/0.60    inference(backward_demodulation,[],[f109,f146])).
% 1.79/0.60  fof(f146,plain,(
% 1.79/0.60    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_8),
% 1.79/0.60    inference(avatar_component_clause,[],[f144])).
% 1.79/0.60  fof(f109,plain,(
% 1.79/0.60    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_6),
% 1.79/0.60    inference(avatar_component_clause,[],[f107])).
% 1.79/0.60  fof(f147,plain,(
% 1.79/0.60    spl5_8 | ~spl5_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f141,f78,f144])).
% 1.79/0.60  fof(f141,plain,(
% 1.79/0.60    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 1.79/0.60    inference(resolution,[],[f40,f80])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f21])).
% 1.79/0.60  fof(f21,plain,(
% 1.79/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.79/0.60  fof(f110,plain,(
% 1.79/0.60    ~spl5_6 | spl5_1),
% 1.79/0.60    inference(avatar_split_clause,[],[f105,f73,f107])).
% 1.79/0.60  fof(f73,plain,(
% 1.79/0.60    spl5_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.79/0.60  fof(f105,plain,(
% 1.79/0.60    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_1),
% 1.79/0.60    inference(forward_demodulation,[],[f75,f28])).
% 1.79/0.60  fof(f28,plain,(
% 1.79/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,axiom,(
% 1.79/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.79/0.60  fof(f75,plain,(
% 1.79/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_1),
% 1.79/0.60    inference(avatar_component_clause,[],[f73])).
% 1.79/0.60  fof(f92,plain,(
% 1.79/0.60    spl5_3 | spl5_4 | ~spl5_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f83,f78,f89,f85])).
% 1.79/0.60  fof(f83,plain,(
% 1.79/0.60    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.79/0.60    inference(resolution,[],[f38,f80])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f81,plain,(
% 1.79/0.60    spl5_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f25,f78])).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f17])).
% 1.79/0.60  fof(f17,negated_conjecture,(
% 1.79/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.79/0.60    inference(negated_conjecture,[],[f16])).
% 1.79/0.60  fof(f16,conjecture,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    ~spl5_1),
% 1.79/0.60    inference(avatar_split_clause,[],[f26,f73])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (13879)------------------------------
% 1.79/0.60  % (13879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (13879)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (13879)Memory used [KB]: 11513
% 1.79/0.60  % (13879)Time elapsed: 0.194 s
% 1.79/0.60  % (13879)------------------------------
% 1.79/0.60  % (13879)------------------------------
% 1.79/0.62  % (13862)Success in time 0.252 s
%------------------------------------------------------------------------------
