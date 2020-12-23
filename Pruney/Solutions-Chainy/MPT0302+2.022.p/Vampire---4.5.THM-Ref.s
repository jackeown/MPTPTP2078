%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:02 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 200 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  241 ( 625 expanded)
%              Number of equality atoms :   51 ( 188 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f292,f356,f473,f474,f523])).

fof(f523,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f520,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK2 != sK3
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK2 != sK3
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f520,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_10 ),
    inference(resolution,[],[f506,f267])).

fof(f267,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f262,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f262,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f259,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f259,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f203,f54])).

fof(f203,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(subsumption_resolution,[],[f200,f53])).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f179,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | sK3 = X0 )
    | ~ spl9_10 ),
    inference(resolution,[],[f503,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f503,plain,
    ( ! [X4] : ~ r2_xboole_0(X4,sK3)
    | ~ spl9_10 ),
    inference(resolution,[],[f298,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f298,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl9_10
  <=> ! [X10] : ~ r2_hidden(X10,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f474,plain,
    ( spl9_10
    | spl9_9 ),
    inference(avatar_split_clause,[],[f454,f294,f297])).

fof(f294,plain,
    ( spl9_9
  <=> ! [X11] :
        ( ~ r2_hidden(X11,sK2)
        | r2_hidden(X11,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f454,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK2)
      | ~ r2_hidden(X5,sK3)
      | r2_hidden(X4,sK3) ) ),
    inference(resolution,[],[f285,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f285,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(superposition,[],[f80,f48])).

fof(f48,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f473,plain,
    ( ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f471,f451])).

fof(f451,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f450,f51])).

fof(f51,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f450,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK2,sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f449,f65])).

fof(f449,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ r2_xboole_0(sK2,sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f369,f75])).

fof(f369,plain,
    ( ! [X26] :
        ( ~ r2_hidden(sK8(sK2,X26),sK3)
        | ~ r2_xboole_0(sK2,X26) )
    | ~ spl9_8 ),
    inference(resolution,[],[f291,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f291,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | ~ r2_hidden(X8,sK3) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl9_8
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK3)
        | r2_hidden(X8,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f471,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,
    ( r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK3)
    | ~ spl9_9 ),
    inference(resolution,[],[f408,f61])).

fof(f408,plain,
    ( ! [X25] :
        ( ~ r2_hidden(sK5(X25,sK3),sK2)
        | r1_tarski(X25,sK3) )
    | ~ spl9_9 ),
    inference(resolution,[],[f295,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f295,plain,
    ( ! [X11] :
        ( r2_hidden(X11,sK3)
        | ~ r2_hidden(X11,sK2) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f294])).

fof(f356,plain,(
    ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f350,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f350,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_7 ),
    inference(resolution,[],[f267,f315])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | sK2 = X0 )
    | ~ spl9_7 ),
    inference(resolution,[],[f310,f65])).

fof(f310,plain,
    ( ! [X4] : ~ r2_xboole_0(X4,sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f288,f75])).

fof(f288,plain,
    ( ! [X9] : ~ r2_hidden(X9,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl9_7
  <=> ! [X9] : ~ r2_hidden(X9,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f292,plain,
    ( spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f272,f290,f287])).

fof(f272,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK2)
      | r2_hidden(X8,sK2) ) ),
    inference(resolution,[],[f80,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(X1,sK2) ) ),
    inference(superposition,[],[f79,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (30839)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (30840)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30827)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (30834)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (30827)Refutation not found, incomplete strategy% (30827)------------------------------
% 0.22/0.53  % (30827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30827)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30827)Memory used [KB]: 1663
% 0.22/0.53  % (30827)Time elapsed: 0.110 s
% 0.22/0.53  % (30827)------------------------------
% 0.22/0.53  % (30827)------------------------------
% 0.22/0.53  % (30847)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (30829)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (30833)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30829)Refutation not found, incomplete strategy% (30829)------------------------------
% 0.22/0.54  % (30829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30838)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (30830)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (30849)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (30854)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (30829)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30829)Memory used [KB]: 10746
% 0.22/0.54  % (30829)Time elapsed: 0.120 s
% 0.22/0.54  % (30829)------------------------------
% 0.22/0.54  % (30829)------------------------------
% 0.22/0.55  % (30851)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (30828)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (30836)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (30855)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (30843)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (30846)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (30836)Refutation not found, incomplete strategy% (30836)------------------------------
% 0.22/0.55  % (30836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30831)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.55  % (30831)Refutation not found, incomplete strategy% (30831)------------------------------
% 1.45/0.55  % (30831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30831)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30831)Memory used [KB]: 6140
% 1.45/0.55  % (30831)Time elapsed: 0.126 s
% 1.45/0.55  % (30831)------------------------------
% 1.45/0.55  % (30831)------------------------------
% 1.45/0.55  % (30836)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30836)Memory used [KB]: 10618
% 1.45/0.55  % (30836)Time elapsed: 0.118 s
% 1.45/0.55  % (30836)------------------------------
% 1.45/0.55  % (30836)------------------------------
% 1.45/0.55  % (30844)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (30844)Refutation not found, incomplete strategy% (30844)------------------------------
% 1.45/0.55  % (30844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30844)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30844)Memory used [KB]: 10618
% 1.45/0.55  % (30844)Time elapsed: 0.128 s
% 1.45/0.55  % (30844)------------------------------
% 1.45/0.55  % (30844)------------------------------
% 1.45/0.55  % (30841)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.55  % (30832)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.55  % (30856)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (30835)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.56  % (30838)Refutation not found, incomplete strategy% (30838)------------------------------
% 1.45/0.56  % (30838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30838)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (30838)Memory used [KB]: 10618
% 1.45/0.56  % (30838)Time elapsed: 0.143 s
% 1.45/0.56  % (30838)------------------------------
% 1.45/0.56  % (30838)------------------------------
% 1.45/0.56  % (30842)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.56  % (30847)Refutation not found, incomplete strategy% (30847)------------------------------
% 1.45/0.56  % (30847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30847)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (30847)Memory used [KB]: 10746
% 1.45/0.56  % (30847)Time elapsed: 0.143 s
% 1.45/0.56  % (30847)------------------------------
% 1.45/0.56  % (30847)------------------------------
% 1.45/0.56  % (30852)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (30848)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (30850)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (30853)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (30837)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.57  % (30837)Refutation not found, incomplete strategy% (30837)------------------------------
% 1.45/0.57  % (30837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (30837)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (30837)Memory used [KB]: 10618
% 1.45/0.57  % (30837)Time elapsed: 0.147 s
% 1.45/0.57  % (30837)------------------------------
% 1.45/0.57  % (30837)------------------------------
% 1.45/0.57  % (30853)Refutation not found, incomplete strategy% (30853)------------------------------
% 1.45/0.57  % (30853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (30853)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (30853)Memory used [KB]: 10746
% 1.45/0.57  % (30853)Time elapsed: 0.134 s
% 1.45/0.57  % (30853)------------------------------
% 1.45/0.57  % (30853)------------------------------
% 1.57/0.57  % (30845)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.58  % (30854)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.59  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f524,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f292,f356,f473,f474,f523])).
% 1.57/0.59  fof(f523,plain,(
% 1.57/0.59    ~spl9_10),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f522])).
% 1.57/0.59  fof(f522,plain,(
% 1.57/0.59    $false | ~spl9_10),
% 1.57/0.59    inference(subsumption_resolution,[],[f520,f50])).
% 1.57/0.59  fof(f50,plain,(
% 1.57/0.59    k1_xboole_0 != sK3),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK2 != sK3 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f18,plain,(
% 1.57/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.57/0.59    inference(flattening,[],[f17])).
% 1.57/0.59  fof(f17,plain,(
% 1.57/0.59    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f15])).
% 1.57/0.59  fof(f15,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.57/0.59    inference(negated_conjecture,[],[f14])).
% 1.57/0.59  fof(f14,conjecture,(
% 1.57/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.57/0.59  fof(f520,plain,(
% 1.57/0.59    k1_xboole_0 = sK3 | ~spl9_10),
% 1.57/0.59    inference(resolution,[],[f506,f267])).
% 1.57/0.59  fof(f267,plain,(
% 1.57/0.59    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.57/0.59    inference(resolution,[],[f262,f61])).
% 1.57/0.59  fof(f61,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f32])).
% 1.57/0.59  fof(f32,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.57/0.59  fof(f31,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(rectify,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.59    inference(nnf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,plain,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.59  fof(f262,plain,(
% 1.57/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.57/0.59    inference(forward_demodulation,[],[f259,f54])).
% 1.57/0.59  fof(f54,plain,(
% 1.57/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f9])).
% 1.57/0.59  fof(f9,axiom,(
% 1.57/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.57/0.59  fof(f259,plain,(
% 1.57/0.59    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.57/0.59    inference(superposition,[],[f203,f54])).
% 1.57/0.59  fof(f203,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)))) )),
% 1.57/0.59    inference(subsumption_resolution,[],[f200,f53])).
% 1.57/0.59  fof(f53,plain,(
% 1.57/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f7])).
% 1.57/0.59  fof(f7,axiom,(
% 1.57/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.57/0.59  fof(f200,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.57/0.59    inference(superposition,[],[f179,f55])).
% 1.57/0.59  fof(f55,plain,(
% 1.57/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.57/0.59  fof(f179,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 1.57/0.59    inference(forward_demodulation,[],[f81,f77])).
% 1.57/0.59  fof(f77,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f8])).
% 1.57/0.59  fof(f8,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.57/0.59  fof(f81,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.57/0.59    inference(definition_unfolding,[],[f59,f57])).
% 1.57/0.59  fof(f57,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.57/0.59  fof(f59,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f27])).
% 1.57/0.59  fof(f27,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f19,plain,(
% 1.57/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f16])).
% 1.57/0.59  fof(f16,plain,(
% 1.57/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.59    inference(rectify,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.57/0.59  fof(f506,plain,(
% 1.57/0.59    ( ! [X0] : (~r1_tarski(X0,sK3) | sK3 = X0) ) | ~spl9_10),
% 1.57/0.59    inference(resolution,[],[f503,f65])).
% 1.57/0.59  fof(f65,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f34])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.57/0.59    inference(flattening,[],[f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.57/0.59    inference(nnf_transformation,[],[f2])).
% 1.57/0.59  fof(f2,axiom,(
% 1.57/0.59    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.57/0.59  fof(f503,plain,(
% 1.57/0.59    ( ! [X4] : (~r2_xboole_0(X4,sK3)) ) | ~spl9_10),
% 1.57/0.59    inference(resolution,[],[f298,f75])).
% 1.57/0.59  fof(f75,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f45,plain,(
% 1.57/0.59    ! [X0,X1] : ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 1.57/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f44])).
% 1.57/0.59  fof(f44,plain,(
% 1.57/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)))),
% 1.57/0.59    introduced(choice_axiom,[])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 1.57/0.59    inference(ennf_transformation,[],[f4])).
% 1.57/0.59  fof(f4,axiom,(
% 1.57/0.59    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 1.57/0.59  fof(f298,plain,(
% 1.57/0.59    ( ! [X10] : (~r2_hidden(X10,sK3)) ) | ~spl9_10),
% 1.57/0.59    inference(avatar_component_clause,[],[f297])).
% 1.57/0.59  fof(f297,plain,(
% 1.57/0.59    spl9_10 <=> ! [X10] : ~r2_hidden(X10,sK3)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.57/0.59  fof(f474,plain,(
% 1.57/0.59    spl9_10 | spl9_9),
% 1.57/0.59    inference(avatar_split_clause,[],[f454,f294,f297])).
% 1.57/0.59  fof(f294,plain,(
% 1.57/0.59    spl9_9 <=> ! [X11] : (~r2_hidden(X11,sK2) | r2_hidden(X11,sK3))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.57/0.59  fof(f454,plain,(
% 1.57/0.59    ( ! [X4,X5] : (~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK3) | r2_hidden(X4,sK3)) )),
% 1.57/0.59    inference(resolution,[],[f285,f79])).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f47])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.57/0.59    inference(flattening,[],[f46])).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.57/0.59    inference(nnf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.57/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.57/0.59  fof(f285,plain,(
% 1.57/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,sK3)) )),
% 1.57/0.59    inference(superposition,[],[f80,f48])).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK3,sK2)),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f80,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f47])).
% 1.57/0.59  fof(f473,plain,(
% 1.57/0.59    ~spl9_8 | ~spl9_9),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f472])).
% 1.57/0.59  fof(f472,plain,(
% 1.57/0.59    $false | (~spl9_8 | ~spl9_9)),
% 1.57/0.59    inference(subsumption_resolution,[],[f471,f451])).
% 1.57/0.59  fof(f451,plain,(
% 1.57/0.59    ~r1_tarski(sK2,sK3) | ~spl9_8),
% 1.57/0.59    inference(subsumption_resolution,[],[f450,f51])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    sK2 != sK3),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f450,plain,(
% 1.57/0.59    sK2 = sK3 | ~r1_tarski(sK2,sK3) | ~spl9_8),
% 1.57/0.59    inference(resolution,[],[f449,f65])).
% 1.57/0.59  fof(f449,plain,(
% 1.57/0.59    ~r2_xboole_0(sK2,sK3) | ~spl9_8),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f446])).
% 1.57/0.59  fof(f446,plain,(
% 1.57/0.59    ~r2_xboole_0(sK2,sK3) | ~r2_xboole_0(sK2,sK3) | ~spl9_8),
% 1.57/0.59    inference(resolution,[],[f369,f75])).
% 1.57/0.59  fof(f369,plain,(
% 1.57/0.59    ( ! [X26] : (~r2_hidden(sK8(sK2,X26),sK3) | ~r2_xboole_0(sK2,X26)) ) | ~spl9_8),
% 1.57/0.59    inference(resolution,[],[f291,f76])).
% 1.57/0.59  fof(f76,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f291,plain,(
% 1.57/0.59    ( ! [X8] : (r2_hidden(X8,sK2) | ~r2_hidden(X8,sK3)) ) | ~spl9_8),
% 1.57/0.59    inference(avatar_component_clause,[],[f290])).
% 1.57/0.59  fof(f290,plain,(
% 1.57/0.59    spl9_8 <=> ! [X8] : (~r2_hidden(X8,sK3) | r2_hidden(X8,sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.57/0.59  fof(f471,plain,(
% 1.57/0.59    r1_tarski(sK2,sK3) | ~spl9_9),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f468])).
% 1.57/0.59  fof(f468,plain,(
% 1.57/0.59    r1_tarski(sK2,sK3) | r1_tarski(sK2,sK3) | ~spl9_9),
% 1.57/0.59    inference(resolution,[],[f408,f61])).
% 1.57/0.59  fof(f408,plain,(
% 1.57/0.59    ( ! [X25] : (~r2_hidden(sK5(X25,sK3),sK2) | r1_tarski(X25,sK3)) ) | ~spl9_9),
% 1.57/0.59    inference(resolution,[],[f295,f62])).
% 1.57/0.59  fof(f62,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f32])).
% 1.57/0.59  fof(f295,plain,(
% 1.57/0.59    ( ! [X11] : (r2_hidden(X11,sK3) | ~r2_hidden(X11,sK2)) ) | ~spl9_9),
% 1.57/0.59    inference(avatar_component_clause,[],[f294])).
% 1.57/0.59  fof(f356,plain,(
% 1.57/0.59    ~spl9_7),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f355])).
% 1.57/0.59  fof(f355,plain,(
% 1.57/0.59    $false | ~spl9_7),
% 1.57/0.59    inference(subsumption_resolution,[],[f350,f49])).
% 1.57/0.59  fof(f49,plain,(
% 1.57/0.59    k1_xboole_0 != sK2),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f350,plain,(
% 1.57/0.59    k1_xboole_0 = sK2 | ~spl9_7),
% 1.57/0.59    inference(resolution,[],[f267,f315])).
% 1.57/0.59  fof(f315,plain,(
% 1.57/0.59    ( ! [X0] : (~r1_tarski(X0,sK2) | sK2 = X0) ) | ~spl9_7),
% 1.57/0.59    inference(resolution,[],[f310,f65])).
% 1.57/0.59  fof(f310,plain,(
% 1.57/0.59    ( ! [X4] : (~r2_xboole_0(X4,sK2)) ) | ~spl9_7),
% 1.57/0.59    inference(resolution,[],[f288,f75])).
% 1.57/0.59  fof(f288,plain,(
% 1.57/0.59    ( ! [X9] : (~r2_hidden(X9,sK2)) ) | ~spl9_7),
% 1.57/0.59    inference(avatar_component_clause,[],[f287])).
% 1.57/0.59  fof(f287,plain,(
% 1.57/0.59    spl9_7 <=> ! [X9] : ~r2_hidden(X9,sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.57/0.59  fof(f292,plain,(
% 1.57/0.59    spl9_7 | spl9_8),
% 1.57/0.59    inference(avatar_split_clause,[],[f272,f290,f287])).
% 1.57/0.59  fof(f272,plain,(
% 1.57/0.59    ( ! [X8,X9] : (~r2_hidden(X8,sK3) | ~r2_hidden(X9,sK2) | r2_hidden(X8,sK2)) )),
% 1.57/0.59    inference(resolution,[],[f80,f125])).
% 1.57/0.59  fof(f125,plain,(
% 1.57/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | r2_hidden(X1,sK2)) )),
% 1.57/0.59    inference(superposition,[],[f79,f48])).
% 1.57/0.59  % SZS output end Proof for theBenchmark
% 1.57/0.59  % (30854)------------------------------
% 1.57/0.59  % (30854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.59  % (30854)Termination reason: Refutation
% 1.57/0.59  
% 1.57/0.59  % (30854)Memory used [KB]: 6524
% 1.57/0.59  % (30854)Time elapsed: 0.163 s
% 1.57/0.59  % (30854)------------------------------
% 1.57/0.59  % (30854)------------------------------
% 1.57/0.59  % (30826)Success in time 0.214 s
%------------------------------------------------------------------------------
