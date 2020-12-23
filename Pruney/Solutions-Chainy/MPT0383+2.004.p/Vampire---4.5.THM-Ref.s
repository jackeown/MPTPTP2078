%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 163 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 ( 658 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f78,f96,f100,f107,f117,f123,f129,f135])).

fof(f135,plain,
    ( ~ spl8_6
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f94,f132])).

fof(f132,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f127,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f94,plain,
    ( r2_hidden(sK7(sK3),sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_6
  <=> r2_hidden(sK7(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f129,plain,
    ( spl8_11
    | ~ spl8_6
    | spl8_9 ),
    inference(avatar_split_clause,[],[f124,f105,f93,f126])).

fof(f105,plain,
    ( spl8_9
  <=> m1_subset_1(sK7(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f124,plain,
    ( ~ r2_hidden(sK7(sK3),sK1)
    | v1_xboole_0(sK1)
    | spl8_9 ),
    inference(resolution,[],[f106,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f106,plain,
    ( ~ m1_subset_1(sK7(sK3),sK1)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f123,plain,
    ( ~ spl8_7
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f99,f120])).

fof(f120,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f115,f32])).

fof(f115,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f99,plain,
    ( r2_hidden(sK6(sK3),sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f117,plain,
    ( spl8_10
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f112,f102,f98,f114])).

fof(f102,plain,
    ( spl8_8
  <=> m1_subset_1(sK6(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f112,plain,
    ( ~ r2_hidden(sK6(sK3),sK0)
    | v1_xboole_0(sK0)
    | spl8_8 ),
    inference(resolution,[],[f103,f35])).

fof(f103,plain,
    ( ~ m1_subset_1(sK6(sK3),sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f107,plain,
    ( ~ spl8_8
    | ~ spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f91,f76,f105,f102])).

fof(f76,plain,
    ( spl8_3
  <=> sK3 = k4_tarski(sK6(sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,
    ( ~ m1_subset_1(sK7(sK3),sK1)
    | ~ m1_subset_1(sK6(sK3),sK0)
    | ~ spl8_3 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK7(sK3),sK1)
    | ~ m1_subset_1(sK6(sK3),sK0)
    | ~ spl8_3 ),
    inference(superposition,[],[f31,f77])).

fof(f77,plain,
    ( sK3 = k4_tarski(sK6(sK3),sK7(sK3))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f31,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f100,plain,
    ( spl8_7
    | ~ spl8_2
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f88,f76,f53,f57,f98])).

fof(f57,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f53,plain,
    ( spl8_1
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f88,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r2_hidden(sK6(sK3),sK0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f65,f77])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X0,sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f64,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f63,f54])).

fof(f54,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f96,plain,
    ( spl8_6
    | ~ spl8_2
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f86,f76,f53,f57,f93])).

fof(f86,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r2_hidden(sK7(sK3),sK1)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f66,f77])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(X0,sK1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f47,f64])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,
    ( spl8_3
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f73,f57,f53,f76])).

fof(f73,plain,
    ( sK3 = k4_tarski(sK6(sK3),sK7(sK3))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f72,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | k4_tarski(sK6(X2),sK7(X2)) = X2 )
    | ~ spl8_1 ),
    inference(resolution,[],[f45,f64])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f12,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f59,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:03:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (32362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.43  % (32370)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.43  % (32362)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f55,f59,f78,f96,f100,f107,f117,f123,f129,f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ~spl8_6 | ~spl8_11),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    $false | (~spl8_6 | ~spl8_11)),
% 0.21/0.43    inference(subsumption_resolution,[],[f94,f132])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl8_11),
% 0.21/0.43    inference(resolution,[],[f127,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(rectify,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    v1_xboole_0(sK1) | ~spl8_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f126])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    spl8_11 <=> v1_xboole_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    r2_hidden(sK7(sK3),sK1) | ~spl8_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl8_6 <=> r2_hidden(sK7(sK3),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl8_11 | ~spl8_6 | spl8_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f124,f105,f93,f126])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    spl8_9 <=> m1_subset_1(sK7(sK3),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    ~r2_hidden(sK7(sK3),sK1) | v1_xboole_0(sK1) | spl8_9),
% 0.21/0.43    inference(resolution,[],[f106,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ~m1_subset_1(sK7(sK3),sK1) | spl8_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f105])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    ~spl8_7 | ~spl8_10),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    $false | (~spl8_7 | ~spl8_10)),
% 0.21/0.43    inference(subsumption_resolution,[],[f99,f120])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl8_10),
% 0.21/0.43    inference(resolution,[],[f115,f32])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    v1_xboole_0(sK0) | ~spl8_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f114])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    spl8_10 <=> v1_xboole_0(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    r2_hidden(sK6(sK3),sK0) | ~spl8_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl8_7 <=> r2_hidden(sK6(sK3),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    spl8_10 | ~spl8_7 | spl8_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f112,f102,f98,f114])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    spl8_8 <=> m1_subset_1(sK6(sK3),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ~r2_hidden(sK6(sK3),sK0) | v1_xboole_0(sK0) | spl8_8),
% 0.21/0.43    inference(resolution,[],[f103,f35])).
% 0.21/0.43  fof(f103,plain,(
% 0.21/0.43    ~m1_subset_1(sK6(sK3),sK0) | spl8_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f102])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ~spl8_8 | ~spl8_9 | ~spl8_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f91,f76,f105,f102])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    spl8_3 <=> sK3 = k4_tarski(sK6(sK3),sK7(sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ~m1_subset_1(sK7(sK3),sK1) | ~m1_subset_1(sK6(sK3),sK0) | ~spl8_3),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f90])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    sK3 != sK3 | ~m1_subset_1(sK7(sK3),sK1) | ~m1_subset_1(sK6(sK3),sK0) | ~spl8_3),
% 0.21/0.43    inference(superposition,[],[f31,f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    sK3 = k4_tarski(sK6(sK3),sK7(sK3)) | ~spl8_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f76])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2)) => (! [X4] : (! [X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1)) | ~m1_subset_1(X4,sK0)) & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) & r2_hidden(sK3,sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    spl8_7 | ~spl8_2 | ~spl8_1 | ~spl8_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f88,f76,f53,f57,f98])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl8_2 <=> r2_hidden(sK3,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl8_1 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ~r2_hidden(sK3,sK2) | r2_hidden(sK6(sK3),sK0) | (~spl8_1 | ~spl8_3)),
% 0.21/0.43    inference(superposition,[],[f65,f77])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK0)) ) | ~spl8_1),
% 0.21/0.43    inference(resolution,[],[f64,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.43    inference(flattening,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.43    inference(nnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl8_1),
% 0.21/0.43    inference(resolution,[],[f63,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl8_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.21/0.43    inference(superposition,[],[f50,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.43    inference(equality_resolution,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.43    inference(rectify,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.43    inference(flattening,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl8_6 | ~spl8_2 | ~spl8_1 | ~spl8_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f86,f76,f53,f57,f93])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ~r2_hidden(sK3,sK2) | r2_hidden(sK7(sK3),sK1) | (~spl8_1 | ~spl8_3)),
% 0.21/0.43    inference(superposition,[],[f66,f77])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,sK1)) ) | ~spl8_1),
% 0.21/0.43    inference(resolution,[],[f47,f64])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f28])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl8_3 | ~spl8_1 | ~spl8_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f73,f57,f53,f76])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    sK3 = k4_tarski(sK6(sK3),sK7(sK3)) | (~spl8_1 | ~spl8_2)),
% 0.21/0.43    inference(resolution,[],[f72,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    r2_hidden(sK3,sK2) | ~spl8_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X2] : (~r2_hidden(X2,sK2) | k4_tarski(sK6(X2),sK7(X2)) = X2) ) | ~spl8_1),
% 0.21/0.43    inference(resolution,[],[f45,f64])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK6(X0),sK7(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f12,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK6(X0),sK7(X0)) = X0)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl8_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    r2_hidden(sK3,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl8_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f53])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (32362)------------------------------
% 0.21/0.43  % (32362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (32362)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (32362)Memory used [KB]: 10618
% 0.21/0.43  % (32362)Time elapsed: 0.044 s
% 0.21/0.43  % (32362)------------------------------
% 0.21/0.43  % (32362)------------------------------
% 0.21/0.43  % (32355)Success in time 0.075 s
%------------------------------------------------------------------------------
