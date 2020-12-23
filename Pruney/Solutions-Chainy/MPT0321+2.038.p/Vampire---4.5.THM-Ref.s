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
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 344 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 (1248 expanded)
%              Number of equality atoms :   74 ( 446 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f121,f145,f186,f231,f237,f302,f310,f324,f383,f420])).

fof(f420,plain,
    ( spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | spl6_1
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f418,f366])).

fof(f366,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f365,f58])).

fof(f58,plain,
    ( sK0 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f365,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK2,sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f361,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f361,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f248,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f248,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,X1),sK2)
        | r1_tarski(sK0,X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f111,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,sK0)
        | r2_hidden(X11,sK2) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_5
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK0)
        | r2_hidden(X11,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f418,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl6_9 ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f329,f42])).

fof(f329,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,X1),sK0)
        | r1_tarski(sK2,X1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f148,f41])).

fof(f148,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK2)
        | r2_hidden(X7,sK0) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_9
  <=> ! [X7] :
        ( ~ r2_hidden(X7,sK2)
        | r2_hidden(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f383,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f381,f344])).

fof(f344,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f343,f62])).

fof(f62,plain,
    ( sK1 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f343,plain,
    ( sK1 = sK3
    | ~ r1_tarski(sK3,sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f342,f39])).

fof(f342,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f130,f42])).

fof(f130,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK1,X1),sK3)
        | r1_tarski(sK1,X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f107,f41])).

fof(f107,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK3) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_4
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK1)
        | r2_hidden(X8,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f381,plain,
    ( r1_tarski(sK3,sK1)
    | ~ spl6_8 ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f257,f42])).

fof(f257,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK3,X1),sK1)
        | r1_tarski(sK3,X1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f144,f41])).

fof(f144,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK3)
        | r2_hidden(X4,sK1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_8
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK3)
        | r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f324,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f322,f150,f147])).

fof(f150,plain,
    ( spl6_10
  <=> ! [X6] : ~ r2_hidden(X6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f322,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X7,sK2)
      | r2_hidden(X7,sK0) ) ),
    inference(resolution,[],[f101,f46])).

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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f48,f29])).

fof(f29,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f310,plain,
    ( spl6_6
    | spl6_5 ),
    inference(avatar_split_clause,[],[f309,f110,f113])).

fof(f113,plain,
    ( spl6_6
  <=> ! [X10] : ~ r2_hidden(X10,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f309,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f46,f29])).

fof(f302,plain,
    ( ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(resolution,[],[f151,f132])).

fof(f132,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f129,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),sK3)
    | k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(resolution,[],[f107,f78])).

fof(f78,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3,k1_xboole_0),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f35,f64])).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f54,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f54,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f151,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f237,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f236,f106,f103])).

fof(f103,plain,
    ( spl6_3
  <=> ! [X9] : ~ r2_hidden(X9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f236,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X1,sK3) ) ),
    inference(superposition,[],[f47,f29])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f231,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f226,f31])).

fof(f226,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(resolution,[],[f114,f78])).

fof(f114,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f186,plain,
    ( ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f181,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f178,f78])).

fof(f178,plain,
    ( ! [X11] : ~ r2_hidden(X11,sK0)
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f177,f64])).

fof(f177,plain,
    ( ! [X11] :
        ( r2_hidden(X11,k1_xboole_0)
        | ~ r2_hidden(X11,sK0) )
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f111,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_7 ),
    inference(resolution,[],[f141,f78])).

fof(f141,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_7
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f145,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f136,f143,f140])).

fof(f136,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X5,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f101,f47])).

fof(f121,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f119,f30])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(resolution,[],[f104,f78])).

fof(f104,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f32,f60,f56])).

fof(f32,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (1686)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 0.21/0.50  % (1683)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.21/0.50  % (1704)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.21/0.50  % (1676)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.21/0.50  % (1704)Refutation not found, incomplete strategy% (1704)------------------------------
% 0.21/0.50  % (1704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1704)Memory used [KB]: 6140
% 0.21/0.50  % (1704)Time elapsed: 0.098 s
% 0.21/0.50  % (1704)------------------------------
% 0.21/0.50  % (1704)------------------------------
% 0.21/0.50  % (1676)Refutation not found, incomplete strategy% (1676)------------------------------
% 0.21/0.50  % (1676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1676)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1676)Memory used [KB]: 6140
% 0.21/0.50  % (1676)Time elapsed: 0.093 s
% 0.21/0.51  % (1676)------------------------------
% 0.21/0.51  % (1676)------------------------------
% 0.21/0.51  % (1696)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.21/0.51  % (1696)Refutation not found, incomplete strategy% (1696)------------------------------
% 0.21/0.51  % (1696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1696)Memory used [KB]: 10618
% 0.21/0.51  % (1696)Time elapsed: 0.102 s
% 0.21/0.51  % (1696)------------------------------
% 0.21/0.51  % (1696)------------------------------
% 0.21/0.51  % (1690)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (1690)Refutation not found, incomplete strategy% (1690)------------------------------
% 0.21/0.51  % (1690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1690)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1690)Memory used [KB]: 6140
% 0.21/0.51  % (1690)Time elapsed: 0.067 s
% 0.21/0.51  % (1690)------------------------------
% 0.21/0.51  % (1690)------------------------------
% 0.21/0.51  % (1681)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.21/0.51  % (1677)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (1684)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.21/0.52  % (1684)Refutation not found, incomplete strategy% (1684)------------------------------
% 0.21/0.52  % (1684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1684)Memory used [KB]: 6140
% 0.21/0.52  % (1684)Time elapsed: 0.107 s
% 0.21/0.52  % (1684)------------------------------
% 0.21/0.52  % (1684)------------------------------
% 0.21/0.52  % (1702)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.21/0.52  % (1682)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.21/0.53  % (1688)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.21/0.53  % (1698)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 0.21/0.53  % (1705)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (1705)Refutation not found, incomplete strategy% (1705)------------------------------
% 0.21/0.53  % (1705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1705)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1705)Memory used [KB]: 10618
% 0.21/0.53  % (1705)Time elapsed: 0.120 s
% 0.21/0.53  % (1705)------------------------------
% 0.21/0.53  % (1705)------------------------------
% 0.21/0.53  % (1680)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.21/0.53  % (1693)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.21/0.53  % (1694)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (1679)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.21/0.53  % (1679)Refutation not found, incomplete strategy% (1679)------------------------------
% 0.21/0.53  % (1679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1679)Memory used [KB]: 6140
% 0.21/0.53  % (1679)Time elapsed: 0.003 s
% 0.21/0.53  % (1679)------------------------------
% 0.21/0.53  % (1679)------------------------------
% 0.21/0.53  % (1694)Refutation not found, incomplete strategy% (1694)------------------------------
% 0.21/0.53  % (1694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1694)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1694)Memory used [KB]: 10618
% 0.21/0.53  % (1694)Time elapsed: 0.124 s
% 0.21/0.53  % (1694)------------------------------
% 0.21/0.53  % (1694)------------------------------
% 0.21/0.53  % (1689)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.21/0.53  % (1678)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.21/0.54  % (1678)Refutation not found, incomplete strategy% (1678)------------------------------
% 0.21/0.54  % (1678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1678)Memory used [KB]: 6140
% 0.21/0.54  % (1678)Time elapsed: 0.129 s
% 0.21/0.54  % (1678)------------------------------
% 0.21/0.54  % (1678)------------------------------
% 1.41/0.54  % (1700)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (1691)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.41/0.54  % (1682)Refutation not found, incomplete strategy% (1682)------------------------------
% 1.41/0.54  % (1682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (1682)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1682)Memory used [KB]: 10618
% 1.41/0.54  % (1682)Time elapsed: 0.101 s
% 1.41/0.54  % (1682)------------------------------
% 1.41/0.54  % (1682)------------------------------
% 1.41/0.54  % (1700)Refutation not found, incomplete strategy% (1700)------------------------------
% 1.41/0.54  % (1700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (1700)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1700)Memory used [KB]: 10618
% 1.41/0.54  % (1700)Time elapsed: 0.131 s
% 1.41/0.54  % (1700)------------------------------
% 1.41/0.54  % (1700)------------------------------
% 1.41/0.54  % (1701)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.54  % (1701)Refutation not found, incomplete strategy% (1701)------------------------------
% 1.41/0.54  % (1701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (1701)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1701)Memory used [KB]: 6140
% 1.41/0.54  % (1701)Time elapsed: 0.130 s
% 1.41/0.54  % (1701)------------------------------
% 1.41/0.54  % (1701)------------------------------
% 1.41/0.54  % (1692)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.41/0.54  % (1697)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.41/0.54  % (1685)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.41/0.54  % (1685)Refutation not found, incomplete strategy% (1685)------------------------------
% 1.41/0.54  % (1685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (1685)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (1685)Memory used [KB]: 6140
% 1.41/0.54  % (1685)Time elapsed: 0.140 s
% 1.41/0.54  % (1685)------------------------------
% 1.41/0.54  % (1685)------------------------------
% 1.41/0.55  % (1699)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.41/0.55  % (1687)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.41/0.55  % (1695)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.41/0.55  % (1703)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.41/0.55  % (1687)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f421,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f63,f121,f145,f186,f231,f237,f302,f310,f324,f383,f420])).
% 1.41/0.55  fof(f420,plain,(
% 1.41/0.55    spl6_1 | ~spl6_5 | ~spl6_9),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f419])).
% 1.41/0.55  fof(f419,plain,(
% 1.41/0.55    $false | (spl6_1 | ~spl6_5 | ~spl6_9)),
% 1.41/0.55    inference(subsumption_resolution,[],[f418,f366])).
% 1.41/0.55  fof(f366,plain,(
% 1.41/0.55    ~r1_tarski(sK2,sK0) | (spl6_1 | ~spl6_5)),
% 1.41/0.55    inference(subsumption_resolution,[],[f365,f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    sK0 != sK2 | spl6_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f56])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    spl6_1 <=> sK0 = sK2),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.55  fof(f365,plain,(
% 1.41/0.55    sK0 = sK2 | ~r1_tarski(sK2,sK0) | ~spl6_5),
% 1.41/0.55    inference(resolution,[],[f361,f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(flattening,[],[f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.55  fof(f361,plain,(
% 1.41/0.55    r1_tarski(sK0,sK2) | ~spl6_5),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f358])).
% 1.41/0.55  fof(f358,plain,(
% 1.41/0.55    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl6_5),
% 1.41/0.55    inference(resolution,[],[f248,f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(rectify,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(nnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.55  fof(f248,plain,(
% 1.41/0.55    ( ! [X1] : (r2_hidden(sK5(sK0,X1),sK2) | r1_tarski(sK0,X1)) ) | ~spl6_5),
% 1.41/0.55    inference(resolution,[],[f111,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    ( ! [X11] : (~r2_hidden(X11,sK0) | r2_hidden(X11,sK2)) ) | ~spl6_5),
% 1.41/0.55    inference(avatar_component_clause,[],[f110])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    spl6_5 <=> ! [X11] : (~r2_hidden(X11,sK0) | r2_hidden(X11,sK2))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.41/0.55  fof(f418,plain,(
% 1.41/0.55    r1_tarski(sK2,sK0) | ~spl6_9),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f415])).
% 1.41/0.55  fof(f415,plain,(
% 1.41/0.55    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0) | ~spl6_9),
% 1.41/0.55    inference(resolution,[],[f329,f42])).
% 1.41/0.55  fof(f329,plain,(
% 1.41/0.55    ( ! [X1] : (r2_hidden(sK5(sK2,X1),sK0) | r1_tarski(sK2,X1)) ) | ~spl6_9),
% 1.41/0.55    inference(resolution,[],[f148,f41])).
% 1.41/0.55  fof(f148,plain,(
% 1.41/0.55    ( ! [X7] : (~r2_hidden(X7,sK2) | r2_hidden(X7,sK0)) ) | ~spl6_9),
% 1.41/0.55    inference(avatar_component_clause,[],[f147])).
% 1.41/0.55  fof(f147,plain,(
% 1.41/0.55    spl6_9 <=> ! [X7] : (~r2_hidden(X7,sK2) | r2_hidden(X7,sK0))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.41/0.55  fof(f383,plain,(
% 1.41/0.55    spl6_2 | ~spl6_4 | ~spl6_8),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f382])).
% 1.41/0.55  fof(f382,plain,(
% 1.41/0.55    $false | (spl6_2 | ~spl6_4 | ~spl6_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f381,f344])).
% 1.41/0.55  fof(f344,plain,(
% 1.41/0.55    ~r1_tarski(sK3,sK1) | (spl6_2 | ~spl6_4)),
% 1.41/0.55    inference(subsumption_resolution,[],[f343,f62])).
% 1.41/0.55  fof(f62,plain,(
% 1.41/0.55    sK1 != sK3 | spl6_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f60])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    spl6_2 <=> sK1 = sK3),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.55  fof(f343,plain,(
% 1.41/0.55    sK1 = sK3 | ~r1_tarski(sK3,sK1) | ~spl6_4),
% 1.41/0.55    inference(resolution,[],[f342,f39])).
% 1.41/0.55  fof(f342,plain,(
% 1.41/0.55    r1_tarski(sK1,sK3) | ~spl6_4),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f339])).
% 1.41/0.55  fof(f339,plain,(
% 1.41/0.55    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl6_4),
% 1.41/0.55    inference(resolution,[],[f130,f42])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    ( ! [X1] : (r2_hidden(sK5(sK1,X1),sK3) | r1_tarski(sK1,X1)) ) | ~spl6_4),
% 1.41/0.55    inference(resolution,[],[f107,f41])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    ( ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,sK3)) ) | ~spl6_4),
% 1.41/0.55    inference(avatar_component_clause,[],[f106])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    spl6_4 <=> ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,sK3))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.41/0.55  fof(f381,plain,(
% 1.41/0.55    r1_tarski(sK3,sK1) | ~spl6_8),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f378])).
% 1.41/0.55  fof(f378,plain,(
% 1.41/0.55    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1) | ~spl6_8),
% 1.41/0.55    inference(resolution,[],[f257,f42])).
% 1.41/0.55  fof(f257,plain,(
% 1.41/0.55    ( ! [X1] : (r2_hidden(sK5(sK3,X1),sK1) | r1_tarski(sK3,X1)) ) | ~spl6_8),
% 1.41/0.55    inference(resolution,[],[f144,f41])).
% 1.41/0.55  fof(f144,plain,(
% 1.41/0.55    ( ! [X4] : (~r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) ) | ~spl6_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f143])).
% 1.41/0.55  fof(f143,plain,(
% 1.41/0.55    spl6_8 <=> ! [X4] : (~r2_hidden(X4,sK3) | r2_hidden(X4,sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.41/0.55  fof(f324,plain,(
% 1.41/0.55    spl6_9 | spl6_10),
% 1.41/0.55    inference(avatar_split_clause,[],[f322,f150,f147])).
% 1.41/0.55  fof(f150,plain,(
% 1.41/0.55    spl6_10 <=> ! [X6] : ~r2_hidden(X6,sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.41/0.55  fof(f322,plain,(
% 1.41/0.55    ( ! [X6,X7] : (~r2_hidden(X6,sK3) | ~r2_hidden(X7,sK2) | r2_hidden(X7,sK0)) )),
% 1.41/0.55    inference(resolution,[],[f101,f46])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.41/0.55    inference(flattening,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.41/0.55    inference(nnf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.41/0.55  fof(f101,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3) | ~r2_hidden(X0,sK2)) )),
% 1.41/0.55    inference(superposition,[],[f48,f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.41/0.55    inference(flattening,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.55    inference(negated_conjecture,[],[f8])).
% 1.41/0.55  fof(f8,conjecture,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f310,plain,(
% 1.41/0.55    spl6_6 | spl6_5),
% 1.41/0.55    inference(avatar_split_clause,[],[f309,f110,f113])).
% 1.41/0.55  fof(f113,plain,(
% 1.41/0.55    spl6_6 <=> ! [X10] : ~r2_hidden(X10,sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.41/0.55  fof(f309,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) )),
% 1.41/0.55    inference(resolution,[],[f73,f48])).
% 1.41/0.55  fof(f73,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) )),
% 1.41/0.55    inference(superposition,[],[f46,f29])).
% 1.41/0.55  fof(f302,plain,(
% 1.41/0.55    ~spl6_4 | ~spl6_10),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f296])).
% 1.41/0.55  fof(f296,plain,(
% 1.41/0.55    $false | (~spl6_4 | ~spl6_10)),
% 1.41/0.55    inference(resolution,[],[f151,f132])).
% 1.41/0.55  fof(f132,plain,(
% 1.41/0.55    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | ~spl6_4),
% 1.41/0.55    inference(subsumption_resolution,[],[f129,f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    k1_xboole_0 != sK1),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    r2_hidden(sK4(sK1,k1_xboole_0),sK3) | k1_xboole_0 = sK1 | ~spl6_4),
% 1.41/0.55    inference(resolution,[],[f107,f78])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    ( ! [X3] : (r2_hidden(sK4(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) )),
% 1.41/0.55    inference(resolution,[],[f35,f64])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(superposition,[],[f54,f33])).
% 1.41/0.55  fof(f33,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 1.41/0.55    inference(equality_resolution,[],[f50])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 1.41/0.55    inference(definition_unfolding,[],[f44,f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.41/0.55    inference(flattening,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.41/0.55    inference(nnf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.41/0.55    inference(nnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.41/0.55  fof(f151,plain,(
% 1.41/0.55    ( ! [X6] : (~r2_hidden(X6,sK3)) ) | ~spl6_10),
% 1.41/0.55    inference(avatar_component_clause,[],[f150])).
% 1.41/0.55  fof(f237,plain,(
% 1.41/0.55    spl6_3 | spl6_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f236,f106,f103])).
% 1.41/0.55  fof(f103,plain,(
% 1.41/0.55    spl6_3 <=> ! [X9] : ~r2_hidden(X9,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.55  fof(f236,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 1.41/0.55    inference(resolution,[],[f74,f48])).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,sK3)) )),
% 1.41/0.55    inference(superposition,[],[f47,f29])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f231,plain,(
% 1.41/0.55    ~spl6_6),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f230])).
% 1.41/0.55  fof(f230,plain,(
% 1.41/0.55    $false | ~spl6_6),
% 1.41/0.55    inference(subsumption_resolution,[],[f226,f31])).
% 1.41/0.55  fof(f226,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | ~spl6_6),
% 1.41/0.55    inference(resolution,[],[f114,f78])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    ( ! [X10] : (~r2_hidden(X10,sK1)) ) | ~spl6_6),
% 1.41/0.55    inference(avatar_component_clause,[],[f113])).
% 1.41/0.55  fof(f186,plain,(
% 1.41/0.55    ~spl6_5 | ~spl6_7),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f185])).
% 1.41/0.55  fof(f185,plain,(
% 1.41/0.55    $false | (~spl6_5 | ~spl6_7)),
% 1.41/0.55    inference(subsumption_resolution,[],[f181,f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    k1_xboole_0 != sK0),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f181,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | (~spl6_5 | ~spl6_7)),
% 1.41/0.55    inference(resolution,[],[f178,f78])).
% 1.41/0.55  fof(f178,plain,(
% 1.41/0.55    ( ! [X11] : (~r2_hidden(X11,sK0)) ) | (~spl6_5 | ~spl6_7)),
% 1.41/0.55    inference(subsumption_resolution,[],[f177,f64])).
% 1.41/0.55  fof(f177,plain,(
% 1.41/0.55    ( ! [X11] : (r2_hidden(X11,k1_xboole_0) | ~r2_hidden(X11,sK0)) ) | (~spl6_5 | ~spl6_7)),
% 1.41/0.55    inference(forward_demodulation,[],[f111,f154])).
% 1.41/0.55  fof(f154,plain,(
% 1.41/0.55    k1_xboole_0 = sK2 | ~spl6_7),
% 1.41/0.55    inference(resolution,[],[f141,f78])).
% 1.41/0.55  fof(f141,plain,(
% 1.41/0.55    ( ! [X5] : (~r2_hidden(X5,sK2)) ) | ~spl6_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f140])).
% 1.41/0.55  fof(f140,plain,(
% 1.41/0.55    spl6_7 <=> ! [X5] : ~r2_hidden(X5,sK2)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.41/0.55  fof(f145,plain,(
% 1.41/0.55    spl6_7 | spl6_8),
% 1.41/0.55    inference(avatar_split_clause,[],[f136,f143,f140])).
% 1.41/0.55  fof(f136,plain,(
% 1.41/0.55    ( ! [X4,X5] : (~r2_hidden(X4,sK3) | ~r2_hidden(X5,sK2) | r2_hidden(X4,sK1)) )),
% 1.41/0.55    inference(resolution,[],[f101,f47])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    ~spl6_3),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f120])).
% 1.41/0.55  fof(f120,plain,(
% 1.41/0.55    $false | ~spl6_3),
% 1.41/0.55    inference(subsumption_resolution,[],[f119,f30])).
% 1.41/0.55  fof(f119,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | ~spl6_3),
% 1.41/0.55    inference(resolution,[],[f104,f78])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    ( ! [X9] : (~r2_hidden(X9,sK0)) ) | ~spl6_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f103])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ~spl6_1 | ~spl6_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f32,f60,f56])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    sK1 != sK3 | sK0 != sK2),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (1687)------------------------------
% 1.41/0.55  % (1687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (1687)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (1687)Memory used [KB]: 6396
% 1.41/0.55  % (1687)Time elapsed: 0.149 s
% 1.41/0.55  % (1687)------------------------------
% 1.41/0.55  % (1687)------------------------------
% 1.57/0.58  % (1675)Success in time 0.212 s
%------------------------------------------------------------------------------
