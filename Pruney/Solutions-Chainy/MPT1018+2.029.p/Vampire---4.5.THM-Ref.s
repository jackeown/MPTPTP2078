%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 186 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  268 ( 830 expanded)
%              Number of equality atoms :   60 ( 211 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f60,f64,f83,f92,f108,f112,f121,f133,f158,f162,f168])).

fof(f168,plain,
    ( ~ spl4_4
    | spl4_1
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f164,f160,f87,f34,f46])).

fof(f46,plain,
    ( spl4_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f34,plain,
    ( spl4_1
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f160,plain,
    ( spl4_22
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f164,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,sK0)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(superposition,[],[f88,f161])).

fof(f161,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f88,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f162,plain,
    ( ~ spl4_3
    | spl4_22
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f151,f87,f38,f160,f42])).

fof(f42,plain,
    ( spl4_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f38,plain,
    ( spl4_2
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f151,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(superposition,[],[f88,f39])).

fof(f39,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f158,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f133,plain,
    ( spl4_18
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f129,f110,f131])).

fof(f131,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f110,plain,
    ( spl4_15
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f129,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_15 ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f67,f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f31,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f111,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f121,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f117,f106,f119])).

fof(f119,plain,
    ( spl4_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f106,plain,
    ( spl4_14
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f117,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14 ),
    inference(resolution,[],[f107,f68])).

fof(f107,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f112,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f96,f90,f42,f110])).

fof(f90,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f96,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(superposition,[],[f43,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f43,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f108,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f95,f90,f46,f106])).

fof(f95,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(superposition,[],[f47,f91])).

fof(f47,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f92,plain,
    ( ~ spl4_6
    | spl4_10
    | spl4_11
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f84,f81,f58,f90,f87,f54])).

fof(f54,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( spl4_7
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f81,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,X2,X0)
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f84,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK1,X2,X0)
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f78,f50,f81,f62])).

fof(f62,plain,
    ( spl4_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f50,plain,
    ( spl4_5
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(sK1,X2,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f32,f51])).

fof(f51,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f64,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f60,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f34])).

fof(f27,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:13:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (9940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (9940)Refutation not found, incomplete strategy% (9940)------------------------------
% 0.20/0.46  % (9940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9940)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (9940)Memory used [KB]: 6012
% 0.20/0.46  % (9940)Time elapsed: 0.003 s
% 0.20/0.46  % (9940)------------------------------
% 0.20/0.46  % (9940)------------------------------
% 0.20/0.46  % (9948)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (9934)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (9939)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (9948)Refutation not found, incomplete strategy% (9948)------------------------------
% 0.20/0.46  % (9948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (9948)Memory used [KB]: 10490
% 0.20/0.46  % (9948)Time elapsed: 0.055 s
% 0.20/0.46  % (9948)------------------------------
% 0.20/0.46  % (9948)------------------------------
% 0.20/0.46  % (9939)Refutation not found, incomplete strategy% (9939)------------------------------
% 0.20/0.46  % (9939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (9939)Memory used [KB]: 10618
% 0.20/0.46  % (9939)Time elapsed: 0.062 s
% 0.20/0.46  % (9939)------------------------------
% 0.20/0.46  % (9939)------------------------------
% 0.20/0.46  % (9934)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f169,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f36,f40,f44,f48,f52,f56,f60,f64,f83,f92,f108,f112,f121,f133,f158,f162,f168])).
% 0.20/0.46  fof(f168,plain,(
% 0.20/0.46    ~spl4_4 | spl4_1 | ~spl4_10 | ~spl4_22),
% 0.20/0.46    inference(avatar_split_clause,[],[f164,f160,f87,f34,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl4_4 <=> r2_hidden(sK2,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl4_1 <=> sK2 = sK3),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl4_10 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.46  fof(f160,plain,(
% 0.20/0.46    spl4_22 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    sK2 = sK3 | ~r2_hidden(sK2,sK0) | (~spl4_10 | ~spl4_22)),
% 0.20/0.46    inference(superposition,[],[f88,f161])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_22),
% 0.20/0.46    inference(avatar_component_clause,[],[f160])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,sK0)) ) | ~spl4_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f87])).
% 0.20/0.46  fof(f162,plain,(
% 0.20/0.46    ~spl4_3 | spl4_22 | ~spl4_2 | ~spl4_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f151,f87,f38,f160,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl4_3 <=> r2_hidden(sK3,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl4_2 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,sK0) | (~spl4_2 | ~spl4_10)),
% 0.20/0.46    inference(superposition,[],[f88,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 0.20/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    spl4_18 | ~spl4_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f129,f110,f131])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    spl4_18 <=> k1_xboole_0 = sK3),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl4_15 <=> r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    k1_xboole_0 = sK3 | ~spl4_15),
% 0.20/0.46    inference(resolution,[],[f111,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(resolution,[],[f67,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~r2_hidden(X1,X0) | k1_xboole_0 = X1) )),
% 0.20/0.46    inference(resolution,[],[f31,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(resolution,[],[f30,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    r2_hidden(sK3,k1_xboole_0) | ~spl4_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f110])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl4_16 | ~spl4_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f117,f106,f119])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    spl4_16 <=> k1_xboole_0 = sK2),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl4_14 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    k1_xboole_0 = sK2 | ~spl4_14),
% 0.20/0.46    inference(resolution,[],[f107,f68])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    r2_hidden(sK2,k1_xboole_0) | ~spl4_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f106])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    spl4_15 | ~spl4_3 | ~spl4_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f96,f90,f42,f110])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl4_11 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    r2_hidden(sK3,k1_xboole_0) | (~spl4_3 | ~spl4_11)),
% 0.20/0.46    inference(superposition,[],[f43,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~spl4_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f90])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    r2_hidden(sK3,sK0) | ~spl4_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f42])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl4_14 | ~spl4_4 | ~spl4_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f95,f90,f46,f106])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    r2_hidden(sK2,k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 0.20/0.46    inference(superposition,[],[f47,f91])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    r2_hidden(sK2,sK0) | ~spl4_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~spl4_6 | spl4_10 | spl4_11 | ~spl4_7 | ~spl4_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f84,f81,f58,f90,f87,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl4_7 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl4_9 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | ~v1_funct_2(sK1,X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl4_7 | ~spl4_9)),
% 0.20/0.46    inference(resolution,[],[f82,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    v1_funct_2(sK1,sK0,sK0) | ~spl4_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f58])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X2,X0) | k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1) ) | ~spl4_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f81])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ~spl4_8 | spl4_9 | ~spl4_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f78,f50,f81,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl4_8 <=> v1_funct_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl4_5 <=> v2_funct_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(sK1,X2,X0) | ~v1_funct_1(sK1)) ) | ~spl4_5),
% 0.20/0.46    inference(resolution,[],[f32,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    v2_funct_1(sK1) | ~spl4_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl4_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f62])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    v1_funct_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f18,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl4_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f58])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    spl4_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f54])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    spl4_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f50])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    v2_funct_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl4_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f46])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    r2_hidden(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl4_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f42])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    r2_hidden(sK3,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f38])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~spl4_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f34])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    sK2 != sK3),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (9934)------------------------------
% 0.20/0.46  % (9934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9934)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (9934)Memory used [KB]: 10746
% 0.20/0.46  % (9934)Time elapsed: 0.005 s
% 0.20/0.46  % (9934)------------------------------
% 0.20/0.46  % (9934)------------------------------
% 0.20/0.46  % (9927)Success in time 0.111 s
%------------------------------------------------------------------------------
