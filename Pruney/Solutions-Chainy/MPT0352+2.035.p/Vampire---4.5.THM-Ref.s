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
% DateTime   : Thu Dec  3 12:44:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 172 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  252 ( 497 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f813,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f72,f77,f86,f107,f162,f239,f240,f452,f695,f769,f774,f777,f794,f812])).

fof(f812,plain,
    ( ~ spl3_1
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | ~ spl3_1
    | spl3_31 ),
    inference(unit_resulting_resolution,[],[f60,f408,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f408,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl3_31
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f60,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f794,plain,
    ( ~ spl3_31
    | spl3_2
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f793,f235,f230,f63,f406])).

fof(f63,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f230,plain,
    ( spl3_19
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f235,plain,
    ( spl3_20
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f793,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f792,f237])).

fof(f237,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f235])).

fof(f792,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f65,f232])).

fof(f232,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f230])).

fof(f65,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f777,plain,
    ( sK1 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ r1_tarski(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f774,plain,
    ( sK1 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f769,plain,
    ( spl3_54
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f749,f406,f764])).

fof(f764,plain,
    ( spl3_54
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f749,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_31 ),
    inference(resolution,[],[f252,f460])).

fof(f460,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_31 ),
    inference(unit_resulting_resolution,[],[f407,f54])).

fof(f407,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f406])).

fof(f252,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,k4_xboole_0(X4,k4_xboole_0(X4,X3)))
      | r1_tarski(X5,X3) ) ),
    inference(superposition,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f695,plain,
    ( spl3_52
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f694,f152,f690])).

fof(f690,plain,
    ( spl3_52
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f152,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f694,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f684,f39])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f684,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_13 ),
    inference(superposition,[],[f57,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f452,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f451,f235,f230,f63,f406])).

fof(f451,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f450,f237])).

fof(f450,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f64,f232])).

fof(f64,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f240,plain,
    ( spl3_19
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f227,f74,f230])).

fof(f74,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f227,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f48,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f48,plain,(
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

fof(f239,plain,
    ( spl3_20
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f226,f69,f235])).

fof(f69,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f226,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f162,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f144,f102,f152])).

fof(f102,plain,
    ( spl3_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f144,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f52,f104])).

fof(f104,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f107,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f106,f83,f102])).

fof(f83,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f99,f38])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f99,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f85,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f85,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f79,f74,f83])).

fof(f79,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f37,f76,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f72,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f63,f59])).

fof(f35,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f63,f59])).

fof(f36,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (28214)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (28201)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (28218)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (28207)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (28212)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (28202)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (28200)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (28199)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.53  % (28210)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (28205)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (28203)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (28216)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (28209)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.54  % (28204)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.54  % (28208)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (28213)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  % (28206)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.54  % (28205)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (28217)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f813,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f66,f67,f72,f77,f86,f107,f162,f239,f240,f452,f695,f769,f774,f777,f794,f812])).
% 0.21/0.56  fof(f812,plain,(
% 0.21/0.56    ~spl3_1 | spl3_31),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f805])).
% 0.21/0.56  fof(f805,plain,(
% 0.21/0.56    $false | (~spl3_1 | spl3_31)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f60,f408,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.21/0.56  fof(f408,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f406])).
% 0.21/0.56  fof(f406,plain,(
% 0.21/0.56    spl3_31 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f794,plain,(
% 0.21/0.56    ~spl3_31 | spl3_2 | ~spl3_19 | ~spl3_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f793,f235,f230,f63,f406])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.56  fof(f230,plain,(
% 0.21/0.56    spl3_19 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.56  fof(f235,plain,(
% 0.21/0.56    spl3_20 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.56  fof(f793,plain,(
% 0.21/0.56    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_19 | ~spl3_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f792,f237])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f235])).
% 0.21/0.56  fof(f792,plain,(
% 0.21/0.56    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_19)),
% 0.21/0.56    inference(forward_demodulation,[],[f65,f232])).
% 0.21/0.56  fof(f232,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f230])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f63])).
% 0.21/0.56  fof(f777,plain,(
% 0.21/0.56    sK1 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~r1_tarski(sK1,sK2)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f774,plain,(
% 0.21/0.56    sK1 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f769,plain,(
% 0.21/0.56    spl3_54 | ~spl3_31),
% 0.21/0.56    inference(avatar_split_clause,[],[f749,f406,f764])).
% 0.21/0.56  fof(f764,plain,(
% 0.21/0.56    spl3_54 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.56  fof(f749,plain,(
% 0.21/0.56    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl3_31),
% 0.21/0.56    inference(resolution,[],[f252,f460])).
% 0.21/0.56  fof(f460,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(X0,k4_xboole_0(sK0,sK2)))) ) | ~spl3_31),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f407,f54])).
% 0.21/0.56  fof(f407,plain,(
% 0.21/0.56    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f406])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~r1_tarski(X5,k4_xboole_0(X4,k4_xboole_0(X4,X3))) | r1_tarski(X5,X3)) )),
% 0.21/0.56    inference(superposition,[],[f55,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f40,f41,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.56  fof(f695,plain,(
% 0.21/0.56    spl3_52 | ~spl3_13),
% 0.21/0.56    inference(avatar_split_clause,[],[f694,f152,f690])).
% 0.21/0.56  fof(f690,plain,(
% 0.21/0.56    spl3_52 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.56  fof(f694,plain,(
% 0.21/0.56    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_13),
% 0.21/0.56    inference(forward_demodulation,[],[f684,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f684,plain,(
% 0.21/0.56    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_13),
% 0.21/0.56    inference(superposition,[],[f57,f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f152])).
% 0.21/0.56  fof(f452,plain,(
% 0.21/0.56    spl3_31 | ~spl3_2 | ~spl3_19 | ~spl3_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f451,f235,f230,f63,f406])).
% 0.21/0.56  fof(f451,plain,(
% 0.21/0.56    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_19 | ~spl3_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f450,f237])).
% 0.21/0.56  fof(f450,plain,(
% 0.21/0.56    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_19)),
% 0.21/0.56    inference(forward_demodulation,[],[f64,f232])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f63])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    spl3_19 | ~spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f227,f74,f230])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.56    inference(resolution,[],[f48,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f74])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    spl3_20 | ~spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f226,f69,f235])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.56    inference(resolution,[],[f48,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f69])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    spl3_13 | ~spl3_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f144,f102,f152])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    spl3_8 <=> r1_tarski(sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_8),
% 0.21/0.56    inference(resolution,[],[f52,f104])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    r1_tarski(sK1,sK0) | ~spl3_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f102])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.56    inference(nnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl3_8 | ~spl3_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f106,f83,f102])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    spl3_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    r1_tarski(sK1,sK0) | ~spl3_5),
% 0.21/0.56    inference(forward_demodulation,[],[f99,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | ~spl3_5),
% 0.21/0.56    inference(resolution,[],[f85,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f83])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    spl3_5 | ~spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f79,f74,f83])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f37,f76,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    spl3_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f33,f74])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f28,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f15])).
% 0.21/0.57  fof(f15,conjecture,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    spl3_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    spl3_1 | spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f35,f63,f59])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ~spl3_1 | ~spl3_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f36,f63,f59])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (28205)------------------------------
% 0.21/0.57  % (28205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28205)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (28205)Memory used [KB]: 6524
% 0.21/0.57  % (28205)Time elapsed: 0.113 s
% 0.21/0.57  % (28205)------------------------------
% 0.21/0.57  % (28205)------------------------------
% 0.21/0.57  % (28194)Success in time 0.207 s
%------------------------------------------------------------------------------
