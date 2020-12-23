%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 148 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  259 ( 504 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f78,f89,f106,f115,f125,f139,f151,f184,f209,f347,f364,f384])).

fof(f384,plain,
    ( ~ spl5_9
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f382,f88])).

fof(f88,plain,
    ( v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_9
  <=> v1_finset_1(sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f382,plain,
    ( ~ v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ spl5_14
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f370,f124])).

fof(f124,plain,
    ( r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_14
  <=> r1_tarski(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f370,plain,
    ( ~ r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ spl5_43 ),
    inference(resolution,[],[f363,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
          | ~ r1_tarski(X3,sK1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(f363,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_43
  <=> r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f364,plain,
    ( spl5_43
    | ~ spl5_24
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f358,f345,f207,f361])).

fof(f207,plain,
    ( spl5_24
  <=> ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f345,plain,
    ( spl5_42
  <=> ! [X3] :
        ( ~ r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3)
        | r1_tarski(sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f358,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))
    | ~ spl5_24
    | ~ spl5_42 ),
    inference(resolution,[],[f346,f208])).

fof(f208,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f346,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3)
        | r1_tarski(sK0,X3) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f345])).

fof(f347,plain,
    ( spl5_42
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f200,f181,f345])).

fof(f181,plain,
    ( spl5_22
  <=> r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f200,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3)
        | r1_tarski(sK0,X3) )
    | ~ spl5_22 ),
    inference(resolution,[],[f183,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f183,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f209,plain,
    ( spl5_24
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f144,f136,f207])).

fof(f136,plain,
    ( spl5_16
  <=> r1_tarski(sK4(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f144,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))
    | ~ spl5_16 ),
    inference(resolution,[],[f138,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f138,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f184,plain,
    ( spl5_22
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f157,f149,f40,f181])).

fof(f40,plain,
    ( spl5_2
  <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f157,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1))) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl5_17
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f79,f35,f149])).

fof(f35,plain,
    ( spl5_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,
    ( v1_finset_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X1)
        & v1_finset_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(f139,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f126,f113,f40,f136])).

fof(f113,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK4(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f126,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f114,f42])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK4(sK0,X0,X1),X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f125,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f120,f104,f40,f122])).

fof(f104,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK3(sK0,X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f120,plain,
    ( r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f105,f42])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK3(sK0,X0,X1),X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f115,plain,
    ( spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f72,f35,f113])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK4(sK0,X0,X1),X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f35,f104])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | r1_tarski(sK3(sK0,X0,X1),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f27,f37])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(sK3(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f84,f76,f40,f86])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | v1_finset_1(sK3(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f84,plain,
    ( v1_finset_1(sK3(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f77,f42])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | v1_finset_1(sK3(sK0,X0,X1)) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f59,f35,f76])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
        | v1_finset_1(sK3(sK0,X0,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f26,f37])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_finset_1(sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (29850)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.44  % (29850)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % (29866)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f385,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f38,f43,f78,f89,f106,f115,f125,f139,f151,f184,f209,f347,f364,f384])).
% 0.22/0.45  fof(f384,plain,(
% 0.22/0.45    ~spl5_9 | ~spl5_14 | ~spl5_43),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f383])).
% 0.22/0.45  fof(f383,plain,(
% 0.22/0.45    $false | (~spl5_9 | ~spl5_14 | ~spl5_43)),
% 0.22/0.45    inference(subsumption_resolution,[],[f382,f88])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    v1_finset_1(sK3(sK0,sK1,sK2)) | ~spl5_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f86])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl5_9 <=> v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.45  fof(f382,plain,(
% 0.22/0.45    ~v1_finset_1(sK3(sK0,sK1,sK2)) | (~spl5_14 | ~spl5_43)),
% 0.22/0.45    inference(subsumption_resolution,[],[f370,f124])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    r1_tarski(sK3(sK0,sK1,sK2),sK1) | ~spl5_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f122])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    spl5_14 <=> r1_tarski(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.45  fof(f370,plain,(
% 0.22/0.45    ~r1_tarski(sK3(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK3(sK0,sK1,sK2)) | ~spl5_43),
% 0.22/0.45    inference(resolution,[],[f363,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) & v1_finset_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.45    inference(negated_conjecture,[],[f5])).
% 0.22/0.45  fof(f5,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).
% 0.22/0.45  fof(f363,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) | ~spl5_43),
% 0.22/0.45    inference(avatar_component_clause,[],[f361])).
% 0.22/0.45  fof(f361,plain,(
% 0.22/0.45    spl5_43 <=> r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.45  fof(f364,plain,(
% 0.22/0.45    spl5_43 | ~spl5_24 | ~spl5_42),
% 0.22/0.45    inference(avatar_split_clause,[],[f358,f345,f207,f361])).
% 0.22/0.45  fof(f207,plain,(
% 0.22/0.45    spl5_24 <=> ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.45  fof(f345,plain,(
% 0.22/0.45    spl5_42 <=> ! [X3] : (~r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3) | r1_tarski(sK0,X3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.22/0.45  fof(f358,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) | (~spl5_24 | ~spl5_42)),
% 0.22/0.45    inference(resolution,[],[f346,f208])).
% 0.22/0.45  fof(f208,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))) ) | ~spl5_24),
% 0.22/0.45    inference(avatar_component_clause,[],[f207])).
% 0.22/0.45  fof(f346,plain,(
% 0.22/0.45    ( ! [X3] : (~r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3) | r1_tarski(sK0,X3)) ) | ~spl5_42),
% 0.22/0.45    inference(avatar_component_clause,[],[f345])).
% 0.22/0.45  fof(f347,plain,(
% 0.22/0.45    spl5_42 | ~spl5_22),
% 0.22/0.45    inference(avatar_split_clause,[],[f200,f181,f345])).
% 0.22/0.45  fof(f181,plain,(
% 0.22/0.45    spl5_22 <=> r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.45  fof(f200,plain,(
% 0.22/0.45    ( ! [X3] : (~r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X3) | r1_tarski(sK0,X3)) ) | ~spl5_22),
% 0.22/0.45    inference(resolution,[],[f183,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.45  fof(f183,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | ~spl5_22),
% 0.22/0.45    inference(avatar_component_clause,[],[f181])).
% 0.22/0.45  fof(f209,plain,(
% 0.22/0.45    spl5_24 | ~spl5_16),
% 0.22/0.45    inference(avatar_split_clause,[],[f144,f136,f207])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    spl5_16 <=> r1_tarski(sK4(sK0,sK1,sK2),sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK4(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))) ) | ~spl5_16),
% 0.22/0.45    inference(resolution,[],[f138,f73])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.45    inference(resolution,[],[f31,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.45    inference(equality_resolution,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~spl5_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f184,plain,(
% 0.22/0.45    spl5_22 | ~spl5_2 | ~spl5_17),
% 0.22/0.45    inference(avatar_split_clause,[],[f157,f149,f40,f181])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl5_2 <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    spl5_17 <=> ! [X1,X0] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) | (~spl5_2 | ~spl5_17)),
% 0.22/0.45    inference(resolution,[],[f150,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl5_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f40])).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1)))) ) | ~spl5_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f149])).
% 0.22/0.45  fof(f151,plain,(
% 0.22/0.45    spl5_17 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f79,f35,f149])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    spl5_1 <=> v1_finset_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1)))) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f30,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    v1_finset_1(sK0) | ~spl5_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f35])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f10,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X1) & v1_finset_1(sK3(X0,X1,X2))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    spl5_16 | ~spl5_2 | ~spl5_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f126,f113,f40,f136])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    spl5_12 <=> ! [X1,X0] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK4(sK0,X0,X1),X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    r1_tarski(sK4(sK0,sK1,sK2),sK2) | (~spl5_2 | ~spl5_12)),
% 0.22/0.45    inference(resolution,[],[f114,f42])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK4(sK0,X0,X1),X1)) ) | ~spl5_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f113])).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    spl5_14 | ~spl5_2 | ~spl5_11),
% 0.22/0.45    inference(avatar_split_clause,[],[f120,f104,f40,f122])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    spl5_11 <=> ! [X1,X0] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK3(sK0,X0,X1),X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    r1_tarski(sK3(sK0,sK1,sK2),sK1) | (~spl5_2 | ~spl5_11)),
% 0.22/0.45    inference(resolution,[],[f105,f42])).
% 0.22/0.45  fof(f105,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK3(sK0,X0,X1),X0)) ) | ~spl5_11),
% 0.22/0.45    inference(avatar_component_clause,[],[f104])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    spl5_12 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f72,f35,f113])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK4(sK0,X0,X1),X1)) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f29,f37])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(sK4(X0,X1,X2),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl5_11 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f62,f35,f104])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK3(sK0,X0,X1),X0)) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f27,f37])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(sK3(X0,X1,X2),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    spl5_9 | ~spl5_2 | ~spl5_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f84,f76,f40,f86])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl5_7 <=> ! [X1,X0] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | v1_finset_1(sK3(sK0,X0,X1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    v1_finset_1(sK3(sK0,sK1,sK2)) | (~spl5_2 | ~spl5_7)),
% 0.22/0.45    inference(resolution,[],[f77,f42])).
% 0.22/0.45  fof(f77,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | v1_finset_1(sK3(sK0,X0,X1))) ) | ~spl5_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f76])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl5_7 | ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f59,f35,f76])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | v1_finset_1(sK3(sK0,X0,X1))) ) | ~spl5_1),
% 0.22/0.45    inference(resolution,[],[f26,f37])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_finset_1(sK3(X0,X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    spl5_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f20,f40])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f35])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    v1_finset_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (29850)------------------------------
% 0.22/0.45  % (29850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (29850)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (29850)Memory used [KB]: 6396
% 0.22/0.45  % (29850)Time elapsed: 0.044 s
% 0.22/0.45  % (29850)------------------------------
% 0.22/0.45  % (29850)------------------------------
% 0.22/0.46  % (29847)Success in time 0.091 s
%------------------------------------------------------------------------------
