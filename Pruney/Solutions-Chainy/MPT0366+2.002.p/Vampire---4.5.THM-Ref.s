%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 144 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  247 ( 544 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f64,f69,f77,f81,f97,f107,f116,f121,f143,f149,f227,f237])).

fof(f237,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f235,f53])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_5
    | spl4_6
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f234,f63])).

fof(f63,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f234,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_6
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f232,f148])).

fof(f148,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_19
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f232,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_6
    | ~ spl4_28 ),
    inference(resolution,[],[f226,f68])).

fof(f68,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_28
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,k3_subset_1(X0,X2))
        | ~ r1_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f227,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f30,f225])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f149,plain,
    ( spl4_19
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f144,f141,f41,f146])).

fof(f41,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f141,plain,
    ( spl4_18
  <=> ! [X10] :
        ( ~ r1_tarski(X10,sK2)
        | r1_xboole_0(X10,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f144,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(resolution,[],[f142,f43])).

fof(f43,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f142,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK2)
        | r1_xboole_0(X10,sK3) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl4_18
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f134,f119,f113,f75,f141])).

fof(f75,plain,
    ( spl4_8
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( spl4_14
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f119,plain,
    ( spl4_15
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f134,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK2)
        | r1_xboole_0(X10,sK3) )
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f130,f76])).

fof(f76,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f130,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,k5_xboole_0(sK2,k1_xboole_0))
        | r1_xboole_0(X10,sK3) )
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(superposition,[],[f120,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
        | r1_xboole_0(X0,X2) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f37,f119])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f116,plain,
    ( spl4_14
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f108,f104,f79,f113])).

fof(f79,plain,
    ( spl4_9
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f104,plain,
    ( spl4_13
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f108,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(superposition,[],[f106,f80])).

fof(f80,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f106,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f102,f95,f46,f104])).

fof(f46,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f102,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f96,f48])).

fof(f48,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f32,f95])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f81,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f36,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f69,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.41  % (28490)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.41  % (28490)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f238,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f44,f49,f54,f64,f69,f77,f81,f97,f107,f116,f121,f143,f149,f227,f237])).
% 0.19/0.41  fof(f237,plain,(
% 0.19/0.41    ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_19 | ~spl4_28),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f236])).
% 0.19/0.41  fof(f236,plain,(
% 0.19/0.41    $false | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_19 | ~spl4_28)),
% 0.19/0.41    inference(subsumption_resolution,[],[f235,f53])).
% 0.19/0.41  fof(f53,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.19/0.41    inference(avatar_component_clause,[],[f51])).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.41  fof(f235,plain,(
% 0.19/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl4_5 | spl4_6 | ~spl4_19 | ~spl4_28)),
% 0.19/0.41    inference(subsumption_resolution,[],[f234,f63])).
% 0.19/0.41  fof(f63,plain,(
% 0.19/0.41    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl4_5),
% 0.19/0.41    inference(avatar_component_clause,[],[f61])).
% 0.19/0.41  fof(f61,plain,(
% 0.19/0.41    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.41  fof(f234,plain,(
% 0.19/0.41    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl4_6 | ~spl4_19 | ~spl4_28)),
% 0.19/0.41    inference(subsumption_resolution,[],[f232,f148])).
% 0.19/0.41  fof(f148,plain,(
% 0.19/0.41    r1_xboole_0(sK1,sK3) | ~spl4_19),
% 0.19/0.41    inference(avatar_component_clause,[],[f146])).
% 0.19/0.41  fof(f146,plain,(
% 0.19/0.41    spl4_19 <=> r1_xboole_0(sK1,sK3)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.41  fof(f232,plain,(
% 0.19/0.41    ~r1_xboole_0(sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl4_6 | ~spl4_28)),
% 0.19/0.41    inference(resolution,[],[f226,f68])).
% 0.19/0.41  fof(f68,plain,(
% 0.19/0.41    ~r1_tarski(sK1,k3_subset_1(sK0,sK3)) | spl4_6),
% 0.19/0.41    inference(avatar_component_clause,[],[f66])).
% 0.19/0.41  fof(f66,plain,(
% 0.19/0.41    spl4_6 <=> r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.41  fof(f226,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_28),
% 0.19/0.41    inference(avatar_component_clause,[],[f225])).
% 0.19/0.41  fof(f225,plain,(
% 0.19/0.41    spl4_28 <=> ! [X1,X0,X2] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.19/0.41  fof(f227,plain,(
% 0.19/0.41    spl4_28),
% 0.19/0.41    inference(avatar_split_clause,[],[f30,f225])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f18])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(nnf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.19/0.41  fof(f149,plain,(
% 0.19/0.41    spl4_19 | ~spl4_1 | ~spl4_18),
% 0.19/0.41    inference(avatar_split_clause,[],[f144,f141,f41,f146])).
% 0.19/0.41  fof(f41,plain,(
% 0.19/0.41    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.41  fof(f141,plain,(
% 0.19/0.41    spl4_18 <=> ! [X10] : (~r1_tarski(X10,sK2) | r1_xboole_0(X10,sK3))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.41  fof(f144,plain,(
% 0.19/0.41    r1_xboole_0(sK1,sK3) | (~spl4_1 | ~spl4_18)),
% 0.19/0.41    inference(resolution,[],[f142,f43])).
% 0.19/0.41  fof(f43,plain,(
% 0.19/0.41    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f41])).
% 0.19/0.41  fof(f142,plain,(
% 0.19/0.41    ( ! [X10] : (~r1_tarski(X10,sK2) | r1_xboole_0(X10,sK3)) ) | ~spl4_18),
% 0.19/0.41    inference(avatar_component_clause,[],[f141])).
% 0.19/0.41  fof(f143,plain,(
% 0.19/0.41    spl4_18 | ~spl4_8 | ~spl4_14 | ~spl4_15),
% 0.19/0.41    inference(avatar_split_clause,[],[f134,f119,f113,f75,f141])).
% 0.19/0.41  fof(f75,plain,(
% 0.19/0.41    spl4_8 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.41  fof(f113,plain,(
% 0.19/0.41    spl4_14 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.41  fof(f119,plain,(
% 0.19/0.41    spl4_15 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.41  fof(f134,plain,(
% 0.19/0.41    ( ! [X10] : (~r1_tarski(X10,sK2) | r1_xboole_0(X10,sK3)) ) | (~spl4_8 | ~spl4_14 | ~spl4_15)),
% 0.19/0.41    inference(forward_demodulation,[],[f130,f76])).
% 0.19/0.41  fof(f76,plain,(
% 0.19/0.41    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_8),
% 0.19/0.41    inference(avatar_component_clause,[],[f75])).
% 0.19/0.41  fof(f130,plain,(
% 0.19/0.41    ( ! [X10] : (~r1_tarski(X10,k5_xboole_0(sK2,k1_xboole_0)) | r1_xboole_0(X10,sK3)) ) | (~spl4_14 | ~spl4_15)),
% 0.19/0.41    inference(superposition,[],[f120,f115])).
% 0.19/0.41  fof(f115,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl4_14),
% 0.19/0.41    inference(avatar_component_clause,[],[f113])).
% 0.19/0.41  fof(f120,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) ) | ~spl4_15),
% 0.19/0.41    inference(avatar_component_clause,[],[f119])).
% 0.19/0.41  fof(f121,plain,(
% 0.19/0.41    spl4_15),
% 0.19/0.41    inference(avatar_split_clause,[],[f37,f119])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 0.19/0.41    inference(definition_unfolding,[],[f35,f29])).
% 0.19/0.41  fof(f29,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.19/0.41  fof(f116,plain,(
% 0.19/0.41    spl4_14 | ~spl4_9 | ~spl4_13),
% 0.19/0.41    inference(avatar_split_clause,[],[f108,f104,f79,f113])).
% 0.19/0.41  fof(f79,plain,(
% 0.19/0.41    spl4_9 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.41  fof(f104,plain,(
% 0.19/0.41    spl4_13 <=> k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.41  fof(f108,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(sK2,sK3) | (~spl4_9 | ~spl4_13)),
% 0.19/0.41    inference(superposition,[],[f106,f80])).
% 0.19/0.41  fof(f80,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_9),
% 0.19/0.41    inference(avatar_component_clause,[],[f79])).
% 0.19/0.41  fof(f106,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(sK3,sK2) | ~spl4_13),
% 0.19/0.41    inference(avatar_component_clause,[],[f104])).
% 0.19/0.41  fof(f107,plain,(
% 0.19/0.41    spl4_13 | ~spl4_2 | ~spl4_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f102,f95,f46,f104])).
% 0.19/0.41  fof(f46,plain,(
% 0.19/0.41    spl4_2 <=> r1_xboole_0(sK3,sK2)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.41  fof(f95,plain,(
% 0.19/0.41    spl4_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.41  fof(f102,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(sK3,sK2) | (~spl4_2 | ~spl4_11)),
% 0.19/0.41    inference(resolution,[],[f96,f48])).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    r1_xboole_0(sK3,sK2) | ~spl4_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f46])).
% 0.19/0.41  fof(f96,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_11),
% 0.19/0.41    inference(avatar_component_clause,[],[f95])).
% 0.19/0.41  fof(f97,plain,(
% 0.19/0.41    spl4_11),
% 0.19/0.41    inference(avatar_split_clause,[],[f32,f95])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.41  fof(f81,plain,(
% 0.19/0.41    spl4_9),
% 0.19/0.41    inference(avatar_split_clause,[],[f28,f79])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.41  fof(f77,plain,(
% 0.19/0.41    spl4_8),
% 0.19/0.41    inference(avatar_split_clause,[],[f39,f75])).
% 0.19/0.41  fof(f39,plain,(
% 0.19/0.41    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.41    inference(forward_demodulation,[],[f36,f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.41  fof(f36,plain,(
% 0.19/0.41    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.19/0.41    inference(definition_unfolding,[],[f27,f29])).
% 0.19/0.41  fof(f27,plain,(
% 0.19/0.41    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.41  fof(f69,plain,(
% 0.19/0.41    ~spl4_6),
% 0.19/0.41    inference(avatar_split_clause,[],[f25,f66])).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f16,f15,f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(flattening,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.19/0.41    inference(negated_conjecture,[],[f8])).
% 0.19/0.41  fof(f8,conjecture,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).
% 0.19/0.41  fof(f64,plain,(
% 0.19/0.41    spl4_5),
% 0.19/0.41    inference(avatar_split_clause,[],[f22,f61])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    spl4_3),
% 0.19/0.41    inference(avatar_split_clause,[],[f20,f51])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    spl4_2),
% 0.19/0.41    inference(avatar_split_clause,[],[f24,f46])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    r1_xboole_0(sK3,sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f44,plain,(
% 0.19/0.41    spl4_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f23,f41])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    r1_tarski(sK1,sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (28490)------------------------------
% 0.19/0.41  % (28490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (28490)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (28490)Memory used [KB]: 6268
% 0.19/0.41  % (28490)Time elapsed: 0.009 s
% 0.19/0.41  % (28490)------------------------------
% 0.19/0.41  % (28490)------------------------------
% 0.19/0.42  % (28482)Success in time 0.075 s
%------------------------------------------------------------------------------
