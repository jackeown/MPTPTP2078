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
% DateTime   : Thu Dec  3 12:46:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 226 expanded)
%              Number of leaves         :   27 (  97 expanded)
%              Depth                    :    8
%              Number of atoms          :  294 ( 667 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f84,f99,f108,f357,f362,f383,f424,f425,f426,f494,f499,f604,f628,f649])).

fof(f649,plain,
    ( ~ spl6_32
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f647,f65])).

fof(f65,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f647,plain,
    ( r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f641,f597])).

fof(f597,plain,
    ( r2_hidden(sK5(sK4,sK3,sK4),sK4)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl6_40
  <=> r2_hidden(sK5(sK4,sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f641,plain,
    ( ~ r2_hidden(sK5(sK4,sK3,sK4),sK4)
    | r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),k1_xboole_0)
    | ~ spl6_32 ),
    inference(resolution,[],[f493,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ r2_hidden(k3_subset_1(X2,X1),X0) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0,X2] :
      ( ( sP0(X1,X3,X0,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X3,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X3,X0,X2] :
      ( sP0(X1,X3,X0,X2)
    <=> ( r2_hidden(X3,X2)
      <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f493,plain,
    ( sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl6_32
  <=> sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f628,plain,
    ( ~ spl6_41
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f618,f496,f600])).

fof(f600,plain,
    ( spl6_41
  <=> r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f496,plain,
    ( spl6_33
  <=> sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f618,plain,
    ( ~ r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4)
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f65,f498,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r2_hidden(k3_subset_1(X2,X1),X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f498,plain,
    ( sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f496])).

fof(f604,plain,
    ( spl6_40
    | spl6_41
    | spl6_28 ),
    inference(avatar_split_clause,[],[f593,f359,f600,f596])).

fof(f359,plain,
    ( spl6_28
  <=> sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f593,plain,
    ( r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4)
    | r2_hidden(sK5(sK4,sK3,sK4),sK4)
    | spl6_28 ),
    inference(resolution,[],[f361,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f361,plain,
    ( ~ sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f359])).

fof(f499,plain,
    ( spl6_33
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f487,f354,f92,f496])).

fof(f92,plain,
    ( spl6_5
  <=> sP1(k1_xboole_0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f354,plain,
    ( spl6_27
  <=> m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f487,plain,
    ( sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f94,f356,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X2,X4,X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ sP0(X1,X3,X0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( sP0(X1,X3,X0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ! [X3] :
          ( sP0(X1,X3,X0,X2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f356,plain,
    ( m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f354])).

fof(f94,plain,
    ( sP1(k1_xboole_0,sK3,sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f494,plain,
    ( spl6_32
    | ~ spl6_7
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f488,f354,f101,f491])).

fof(f101,plain,
    ( spl6_7
  <=> sP1(sK4,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f488,plain,
    ( sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4)
    | ~ spl6_7
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f103,f356,f38])).

fof(f103,plain,
    ( sP1(sK4,sK3,k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f426,plain,
    ( spl6_30
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f392,f61,f380])).

fof(f380,plain,
    ( spl6_30
  <=> sP2(sK4,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f61,plain,
    ( spl6_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f392,plain,
    ( sP2(sK4,sK3,sK4)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f63,f63,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X1,X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f12,f17,f16,f15])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f63,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f425,plain,
    ( spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f394,f61,f105])).

fof(f105,plain,
    ( spl6_8
  <=> sP2(k1_xboole_0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f394,plain,
    ( sP2(k1_xboole_0,sK3,sK4)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f33,f63,f45])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f424,plain,
    ( spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f397,f61,f96])).

fof(f96,plain,
    ( spl6_6
  <=> sP2(sK4,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f397,plain,
    ( sP2(sK4,sK3,k1_xboole_0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f63,f33,f45])).

fof(f383,plain,
    ( ~ spl6_30
    | ~ spl6_1
    | spl6_2
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f371,f334,f56,f51,f380])).

fof(f51,plain,
    ( spl6_1
  <=> k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f56,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f334,plain,
    ( spl6_26
  <=> sP1(sK4,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f371,plain,
    ( ~ sP2(sK4,sK3,sK4)
    | ~ spl6_1
    | spl6_2
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f58,f335,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ sP2(sK4,sK3,X0)
        | ~ sP1(X0,sK3,sK4)
        | k1_xboole_0 = X0 )
    | ~ spl6_1 ),
    inference(superposition,[],[f37,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X1,X0) = X2
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X0) = X2
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k7_setfam_1(X1,X0) != X2 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP1(X2,X0,X1) )
        & ( sP1(X2,X0,X1)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f335,plain,
    ( sP1(sK4,sK3,sK4)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f334])).

fof(f58,plain,
    ( k1_xboole_0 != sK4
    | spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f362,plain,
    ( ~ spl6_28
    | spl6_26 ),
    inference(avatar_split_clause,[],[f351,f334,f359])).

fof(f351,plain,
    ( ~ sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4)
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f336,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,sK5(X0,X1,X2),X1,X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f336,plain,
    ( ~ sP1(sK4,sK3,sK4)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f334])).

fof(f357,plain,
    ( spl6_27
    | spl6_26 ),
    inference(avatar_split_clause,[],[f352,f334,f354])).

fof(f352,plain,
    ( m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3))
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f336,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f88,f79,f105,f101])).

fof(f79,plain,
    ( spl6_4
  <=> sK4 = k7_setfam_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( ~ sP2(k1_xboole_0,sK3,sK4)
    | sP1(sK4,sK3,k1_xboole_0)
    | ~ spl6_4 ),
    inference(superposition,[],[f49,f81])).

fof(f81,plain,
    ( sK4 = k7_setfam_1(sK3,k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1,k7_setfam_1(X1,X0))
      | sP1(k7_setfam_1(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k7_setfam_1(X1,X0) != X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( spl6_5
    | ~ spl6_6
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f87,f51,f96,f92])).

fof(f87,plain,
    ( ~ sP2(sK4,sK3,k1_xboole_0)
    | sP1(k1_xboole_0,sK3,sK4)
    | ~ spl6_1 ),
    inference(superposition,[],[f49,f53])).

fof(f84,plain,
    ( spl6_4
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f83,f61,f51,f79])).

fof(f83,plain,
    ( sK4 = k7_setfam_1(sK3,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f76,f63])).

fof(f76,plain,
    ( sK4 = k7_setfam_1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl6_1 ),
    inference(superposition,[],[f35,f53])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f64,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f59,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (15475)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (15475)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f650,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f54,f59,f64,f84,f99,f108,f357,f362,f383,f424,f425,f426,f494,f499,f604,f628,f649])).
% 0.21/0.44  fof(f649,plain,(
% 0.21/0.44    ~spl6_32 | ~spl6_40),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f648])).
% 0.21/0.44  fof(f648,plain,(
% 0.21/0.44    $false | (~spl6_32 | ~spl6_40)),
% 0.21/0.44    inference(subsumption_resolution,[],[f647,f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f34,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.44  fof(f647,plain,(
% 0.21/0.44    r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),k1_xboole_0) | (~spl6_32 | ~spl6_40)),
% 0.21/0.44    inference(subsumption_resolution,[],[f641,f597])).
% 0.21/0.44  fof(f597,plain,(
% 0.21/0.44    r2_hidden(sK5(sK4,sK3,sK4),sK4) | ~spl6_40),
% 0.21/0.44    inference(avatar_component_clause,[],[f596])).
% 0.21/0.44  fof(f596,plain,(
% 0.21/0.44    spl6_40 <=> r2_hidden(sK5(sK4,sK3,sK4),sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.44  fof(f641,plain,(
% 0.21/0.44    ~r2_hidden(sK5(sK4,sK3,sK4),sK4) | r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),k1_xboole_0) | ~spl6_32),
% 0.21/0.44    inference(resolution,[],[f493,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r2_hidden(X1,X3) | r2_hidden(k3_subset_1(X2,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3)) & (r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0)) & (r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.44    inference(rectify,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X1,X3,X0,X2] : ((sP0(X1,X3,X0,X2) | ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~sP0(X1,X3,X0,X2)))),
% 0.21/0.44    inference(nnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X1,X3,X0,X2] : (sP0(X1,X3,X0,X2) <=> (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.44  fof(f493,plain,(
% 0.21/0.44    sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4) | ~spl6_32),
% 0.21/0.44    inference(avatar_component_clause,[],[f491])).
% 0.21/0.44  fof(f491,plain,(
% 0.21/0.44    spl6_32 <=> sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.44  fof(f628,plain,(
% 0.21/0.44    ~spl6_41 | ~spl6_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f618,f496,f600])).
% 0.21/0.44  fof(f600,plain,(
% 0.21/0.44    spl6_41 <=> r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.44  fof(f496,plain,(
% 0.21/0.44    spl6_33 <=> sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.44  fof(f618,plain,(
% 0.21/0.44    ~r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4) | ~spl6_33),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f65,f498,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f498,plain,(
% 0.21/0.44    sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0) | ~spl6_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f496])).
% 0.21/0.44  fof(f604,plain,(
% 0.21/0.44    spl6_40 | spl6_41 | spl6_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f593,f359,f600,f596])).
% 0.21/0.44  fof(f359,plain,(
% 0.21/0.44    spl6_28 <=> sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.44  fof(f593,plain,(
% 0.21/0.44    r2_hidden(k3_subset_1(sK3,sK5(sK4,sK3,sK4)),sK4) | r2_hidden(sK5(sK4,sK3,sK4),sK4) | spl6_28),
% 0.21/0.44    inference(resolution,[],[f361,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f361,plain,(
% 0.21/0.44    ~sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4) | spl6_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f359])).
% 0.21/0.44  fof(f499,plain,(
% 0.21/0.44    spl6_33 | ~spl6_5 | ~spl6_27),
% 0.21/0.44    inference(avatar_split_clause,[],[f487,f354,f92,f496])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl6_5 <=> sP1(k1_xboole_0,sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.44  fof(f354,plain,(
% 0.21/0.44    spl6_27 <=> m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.44  fof(f487,plain,(
% 0.21/0.44    sP0(sK4,sK5(sK4,sK3,sK4),sK3,k1_xboole_0) | (~spl6_5 | ~spl6_27)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f94,f356,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1)) | ~sP1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,sK5(X0,X1,X2),X1,X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1))) => (~sP0(X2,sK5(X0,X1,X2),X1,X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.44    inference(rectify,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ? [X3] : (~sP0(X1,X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP1(X2,X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> ! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.44  fof(f356,plain,(
% 0.21/0.44    m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3)) | ~spl6_27),
% 0.21/0.44    inference(avatar_component_clause,[],[f354])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    sP1(k1_xboole_0,sK3,sK4) | ~spl6_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f494,plain,(
% 0.21/0.44    spl6_32 | ~spl6_7 | ~spl6_27),
% 0.21/0.44    inference(avatar_split_clause,[],[f488,f354,f101,f491])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl6_7 <=> sP1(sK4,sK3,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.44  fof(f488,plain,(
% 0.21/0.44    sP0(k1_xboole_0,sK5(sK4,sK3,sK4),sK3,sK4) | (~spl6_7 | ~spl6_27)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f103,f356,f38])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    sP1(sK4,sK3,k1_xboole_0) | ~spl6_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f101])).
% 0.21/0.44  fof(f426,plain,(
% 0.21/0.44    spl6_30 | ~spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f392,f61,f380])).
% 0.21/0.44  fof(f380,plain,(
% 0.21/0.44    spl6_30 <=> sP2(sK4,sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl6_3 <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.44  fof(f392,plain,(
% 0.21/0.44    sP2(sK4,sK3,sK4) | ~spl6_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f63,f63,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP2(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(definition_folding,[],[f12,f17,f16,f15])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X1,X0,X2] : ((k7_setfam_1(X0,X1) = X2 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0,X2))),
% 0.21/0.44    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) | ~spl6_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f61])).
% 0.21/0.44  fof(f425,plain,(
% 0.21/0.44    spl6_8 | ~spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f394,f61,f105])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl6_8 <=> sP2(k1_xboole_0,sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.44  fof(f394,plain,(
% 0.21/0.44    sP2(k1_xboole_0,sK3,sK4) | ~spl6_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f33,f63,f45])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.44  fof(f424,plain,(
% 0.21/0.44    spl6_6 | ~spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f397,f61,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    spl6_6 <=> sP2(sK4,sK3,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.44  fof(f397,plain,(
% 0.21/0.44    sP2(sK4,sK3,k1_xboole_0) | ~spl6_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f63,f33,f45])).
% 0.21/0.44  fof(f383,plain,(
% 0.21/0.44    ~spl6_30 | ~spl6_1 | spl6_2 | ~spl6_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f371,f334,f56,f51,f380])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl6_1 <=> k1_xboole_0 = k7_setfam_1(sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl6_2 <=> k1_xboole_0 = sK4),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.44  fof(f334,plain,(
% 0.21/0.44    spl6_26 <=> sP1(sK4,sK3,sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.44  fof(f371,plain,(
% 0.21/0.44    ~sP2(sK4,sK3,sK4) | (~spl6_1 | spl6_2 | ~spl6_26)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f58,f335,f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ( ! [X0] : (~sP2(sK4,sK3,X0) | ~sP1(X0,sK3,sK4) | k1_xboole_0 = X0) ) | ~spl6_1),
% 0.21/0.44    inference(superposition,[],[f37,f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    k1_xboole_0 = k7_setfam_1(sK3,sK4) | ~spl6_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f51])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2)) | ~sP2(X0,X1,X2))),
% 0.21/0.44    inference(rectify,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X1,X0,X2] : (((k7_setfam_1(X0,X1) = X2 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k7_setfam_1(X0,X1) != X2)) | ~sP2(X1,X0,X2))),
% 0.21/0.44    inference(nnf_transformation,[],[f17])).
% 0.21/0.44  fof(f335,plain,(
% 0.21/0.44    sP1(sK4,sK3,sK4) | ~spl6_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f334])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    k1_xboole_0 != sK4 | spl6_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f56])).
% 0.21/0.44  fof(f362,plain,(
% 0.21/0.44    ~spl6_28 | spl6_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f351,f334,f359])).
% 0.21/0.44  fof(f351,plain,(
% 0.21/0.44    ~sP0(sK4,sK5(sK4,sK3,sK4),sK3,sK4) | spl6_26),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f336,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~sP0(X2,sK5(X0,X1,X2),X1,X0) | sP1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f336,plain,(
% 0.21/0.44    ~sP1(sK4,sK3,sK4) | spl6_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f334])).
% 0.21/0.44  fof(f357,plain,(
% 0.21/0.44    spl6_27 | spl6_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f352,f334,f354])).
% 0.21/0.44  fof(f352,plain,(
% 0.21/0.44    m1_subset_1(sK5(sK4,sK3,sK4),k1_zfmisc_1(sK3)) | spl6_26),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f336,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(X1)) | sP1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl6_7 | ~spl6_8 | ~spl6_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f88,f79,f105,f101])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl6_4 <=> sK4 = k7_setfam_1(sK3,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ~sP2(k1_xboole_0,sK3,sK4) | sP1(sK4,sK3,k1_xboole_0) | ~spl6_4),
% 0.21/0.44    inference(superposition,[],[f49,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    sK4 = k7_setfam_1(sK3,k1_xboole_0) | ~spl6_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sP2(X0,X1,k7_setfam_1(X1,X0)) | sP1(k7_setfam_1(X1,X0),X1,X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2 | ~sP2(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl6_5 | ~spl6_6 | ~spl6_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f87,f51,f96,f92])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    ~sP2(sK4,sK3,k1_xboole_0) | sP1(k1_xboole_0,sK3,sK4) | ~spl6_1),
% 0.21/0.44    inference(superposition,[],[f49,f53])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl6_4 | ~spl6_1 | ~spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f83,f61,f51,f79])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    sK4 = k7_setfam_1(sK3,k1_xboole_0) | (~spl6_1 | ~spl6_3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f76,f63])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    sK4 = k7_setfam_1(sK3,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) | ~spl6_1),
% 0.21/0.44    inference(superposition,[],[f35,f53])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ~spl6_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f31,f56])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    k1_xboole_0 != sK4),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl6_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f32,f51])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    k1_xboole_0 = k7_setfam_1(sK3,sK4)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (15475)------------------------------
% 0.21/0.44  % (15475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (15475)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (15475)Memory used [KB]: 11001
% 0.21/0.44  % (15475)Time elapsed: 0.019 s
% 0.21/0.44  % (15475)------------------------------
% 0.21/0.44  % (15475)------------------------------
% 0.21/0.45  % (15458)Success in time 0.087 s
%------------------------------------------------------------------------------
