%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:44 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 211 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  263 ( 681 expanded)
%              Number of equality atoms :   47 ( 113 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f250,f316,f341,f416,f434,f513])).

fof(f513,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f511,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f511,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f509])).

fof(f509,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f365,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f365,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK0,X9),sK2)
        | r1_tarski(sK0,X9) )
    | ~ spl7_6 ),
    inference(resolution,[],[f214,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f214,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,sK2) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_6
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f434,plain,
    ( spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f432,f65])).

fof(f65,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f432,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f354,f46])).

fof(f354,plain,
    ( ! [X9] :
        ( r2_hidden(sK6(sK1,X9),sK3)
        | r1_tarski(sK1,X9) )
    | ~ spl7_3 ),
    inference(resolution,[],[f204,f45])).

fof(f204,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK3) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_3
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f416,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f414,f213,f210])).

fof(f210,plain,
    ( spl7_5
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f414,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f160,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f111,f33])).

fof(f33,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f111,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X9),X12)
      | ~ r2_hidden(X10,X11)
      | r2_hidden(k4_tarski(X10,X8),X12)
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f341,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f338,f206,f203])).

fof(f206,plain,
    ( spl7_4
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f160,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f316,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f312,f57])).

fof(f57,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f312,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f34,f286])).

fof(f286,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(resolution,[],[f207,f91])).

fof(f91,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3,k1_xboole_0),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f42,f79])).

fof(f79,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f78,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f53,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f78,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f54,f38])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f206])).

fof(f34,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f250,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f246,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f246,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f34,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_5 ),
    inference(resolution,[],[f211,f91])).

fof(f211,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f66,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f63,f59])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.36/0.57  % (3704)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.57  % (3696)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.59/0.59  % (3688)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.59/0.59  % (3707)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.59/0.59  % (3699)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.59/0.59  % (3707)Refutation not found, incomplete strategy% (3707)------------------------------
% 1.59/0.59  % (3707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (3691)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.59/0.60  % (3684)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.59/0.60  % (3685)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.59/0.60  % (3686)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 1.59/0.60  % (3699)Refutation not found, incomplete strategy% (3699)------------------------------
% 1.59/0.60  % (3699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (3707)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (3707)Memory used [KB]: 10746
% 1.59/0.60  % (3707)Time elapsed: 0.161 s
% 1.59/0.60  % (3707)------------------------------
% 1.59/0.60  % (3707)------------------------------
% 1.59/0.60  % (3699)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (3699)Memory used [KB]: 10618
% 1.59/0.60  % (3699)Time elapsed: 0.159 s
% 1.59/0.60  % (3699)------------------------------
% 1.59/0.60  % (3699)------------------------------
% 1.59/0.60  % (3687)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 1.59/0.61  % (3683)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.59/0.62  % (3681)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 1.59/0.63  % (3709)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.59/0.63  % (3682)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.59/0.63  % (3703)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.59/0.63  % (3697)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.59/0.63  % (3700)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.59/0.63  % (3701)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.59/0.63  % (3694)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.59/0.63  % (3700)Refutation not found, incomplete strategy% (3700)------------------------------
% 1.59/0.63  % (3700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  % (3700)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.63  
% 1.59/0.63  % (3700)Memory used [KB]: 1663
% 1.59/0.63  % (3700)Time elapsed: 0.204 s
% 1.59/0.63  % (3700)------------------------------
% 1.59/0.63  % (3700)------------------------------
% 1.59/0.64  % (3689)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.59/0.64  % (3689)Refutation not found, incomplete strategy% (3689)------------------------------
% 1.59/0.64  % (3689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.64  % (3689)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.64  
% 1.59/0.64  % (3689)Memory used [KB]: 6140
% 1.59/0.64  % (3689)Time elapsed: 0.204 s
% 1.59/0.64  % (3689)------------------------------
% 1.59/0.64  % (3689)------------------------------
% 1.59/0.64  % (3692)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.59/0.64  % (3690)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.59/0.64  % (3702)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.59/0.64  % (3710)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.59/0.64  % (3693)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.59/0.65  % (3695)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 1.59/0.65  % (3695)Refutation not found, incomplete strategy% (3695)------------------------------
% 1.59/0.65  % (3695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (3706)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 2.21/0.65  % (3705)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.21/0.65  % (3705)Refutation not found, incomplete strategy% (3705)------------------------------
% 2.21/0.65  % (3705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (3698)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 2.21/0.65  % (3695)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.65  
% 2.21/0.65  % (3695)Memory used [KB]: 6140
% 2.21/0.65  % (3695)Time elapsed: 0.213 s
% 2.21/0.65  % (3695)------------------------------
% 2.21/0.65  % (3695)------------------------------
% 2.21/0.66  % (3708)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 2.21/0.66  % (3705)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (3705)Memory used [KB]: 10618
% 2.21/0.66  % (3705)Time elapsed: 0.214 s
% 2.21/0.66  % (3705)------------------------------
% 2.21/0.66  % (3705)------------------------------
% 2.21/0.67  % (3698)Refutation not found, incomplete strategy% (3698)------------------------------
% 2.21/0.67  % (3698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (3698)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.67  
% 2.21/0.67  % (3698)Memory used [KB]: 6140
% 2.21/0.67  % (3698)Time elapsed: 0.237 s
% 2.21/0.67  % (3698)------------------------------
% 2.21/0.67  % (3698)------------------------------
% 2.21/0.67  % (3692)Refutation found. Thanks to Tanya!
% 2.21/0.67  % SZS status Theorem for theBenchmark
% 2.39/0.68  % SZS output start Proof for theBenchmark
% 2.39/0.68  fof(f514,plain,(
% 2.39/0.68    $false),
% 2.39/0.68    inference(avatar_sat_refutation,[],[f66,f250,f316,f341,f416,f434,f513])).
% 2.39/0.68  fof(f513,plain,(
% 2.39/0.68    spl7_1 | ~spl7_6),
% 2.39/0.68    inference(avatar_contradiction_clause,[],[f512])).
% 2.39/0.68  fof(f512,plain,(
% 2.39/0.68    $false | (spl7_1 | ~spl7_6)),
% 2.39/0.68    inference(subsumption_resolution,[],[f511,f61])).
% 2.39/0.68  fof(f61,plain,(
% 2.39/0.68    ~r1_tarski(sK0,sK2) | spl7_1),
% 2.39/0.68    inference(avatar_component_clause,[],[f59])).
% 2.39/0.68  fof(f59,plain,(
% 2.39/0.68    spl7_1 <=> r1_tarski(sK0,sK2)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.39/0.68  fof(f511,plain,(
% 2.39/0.68    r1_tarski(sK0,sK2) | ~spl7_6),
% 2.39/0.68    inference(duplicate_literal_removal,[],[f509])).
% 2.39/0.68  fof(f509,plain,(
% 2.39/0.68    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2) | ~spl7_6),
% 2.39/0.68    inference(resolution,[],[f365,f46])).
% 2.39/0.68  fof(f46,plain,(
% 2.39/0.68    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f28])).
% 2.39/0.68  fof(f28,plain,(
% 2.39/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 2.39/0.68  fof(f27,plain,(
% 2.39/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f26,plain,(
% 2.39/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/0.68    inference(rectify,[],[f25])).
% 2.39/0.68  fof(f25,plain,(
% 2.39/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.39/0.68    inference(nnf_transformation,[],[f17])).
% 2.39/0.68  fof(f17,plain,(
% 2.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.39/0.68    inference(ennf_transformation,[],[f1])).
% 2.39/0.68  fof(f1,axiom,(
% 2.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.39/0.68  fof(f365,plain,(
% 2.39/0.68    ( ! [X9] : (r2_hidden(sK6(sK0,X9),sK2) | r1_tarski(sK0,X9)) ) | ~spl7_6),
% 2.39/0.68    inference(resolution,[],[f214,f45])).
% 2.39/0.68  fof(f45,plain,(
% 2.39/0.68    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f28])).
% 2.39/0.68  fof(f214,plain,(
% 2.39/0.68    ( ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(X2,sK2)) ) | ~spl7_6),
% 2.39/0.68    inference(avatar_component_clause,[],[f213])).
% 2.39/0.68  fof(f213,plain,(
% 2.39/0.68    spl7_6 <=> ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(X2,sK2))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.39/0.68  fof(f434,plain,(
% 2.39/0.68    spl7_2 | ~spl7_3),
% 2.39/0.68    inference(avatar_contradiction_clause,[],[f433])).
% 2.39/0.68  fof(f433,plain,(
% 2.39/0.68    $false | (spl7_2 | ~spl7_3)),
% 2.39/0.68    inference(subsumption_resolution,[],[f432,f65])).
% 2.39/0.68  fof(f65,plain,(
% 2.39/0.68    ~r1_tarski(sK1,sK3) | spl7_2),
% 2.39/0.68    inference(avatar_component_clause,[],[f63])).
% 2.39/0.68  fof(f63,plain,(
% 2.39/0.68    spl7_2 <=> r1_tarski(sK1,sK3)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.39/0.68  fof(f432,plain,(
% 2.39/0.68    r1_tarski(sK1,sK3) | ~spl7_3),
% 2.39/0.68    inference(duplicate_literal_removal,[],[f430])).
% 2.39/0.68  fof(f430,plain,(
% 2.39/0.68    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3) | ~spl7_3),
% 2.39/0.68    inference(resolution,[],[f354,f46])).
% 2.39/0.68  fof(f354,plain,(
% 2.39/0.68    ( ! [X9] : (r2_hidden(sK6(sK1,X9),sK3) | r1_tarski(sK1,X9)) ) | ~spl7_3),
% 2.39/0.68    inference(resolution,[],[f204,f45])).
% 2.39/0.68  fof(f204,plain,(
% 2.39/0.68    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK3)) ) | ~spl7_3),
% 2.39/0.68    inference(avatar_component_clause,[],[f203])).
% 2.39/0.68  fof(f203,plain,(
% 2.39/0.68    spl7_3 <=> ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK3))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.39/0.68  fof(f416,plain,(
% 2.39/0.68    spl7_5 | spl7_6),
% 2.39/0.68    inference(avatar_split_clause,[],[f414,f213,f210])).
% 2.39/0.68  fof(f210,plain,(
% 2.39/0.68    spl7_5 <=> ! [X3] : ~r2_hidden(X3,sK1)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.39/0.68  fof(f414,plain,(
% 2.39/0.68    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X2,sK2)) )),
% 2.39/0.68    inference(resolution,[],[f160,f50])).
% 2.39/0.68  fof(f50,plain,(
% 2.39/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f32])).
% 2.39/0.68  fof(f32,plain,(
% 2.39/0.68    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.39/0.68    inference(flattening,[],[f31])).
% 2.39/0.68  fof(f31,plain,(
% 2.39/0.68    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.39/0.68    inference(nnf_transformation,[],[f8])).
% 2.39/0.68  fof(f8,axiom,(
% 2.39/0.68    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.39/0.68  fof(f160,plain,(
% 2.39/0.68    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK1)) )),
% 2.39/0.68    inference(resolution,[],[f111,f33])).
% 2.39/0.68  fof(f33,plain,(
% 2.39/0.68    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.39/0.68    inference(cnf_transformation,[],[f19])).
% 2.39/0.68  fof(f19,plain,(
% 2.39/0.68    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).
% 2.39/0.68  fof(f18,plain,(
% 2.39/0.68    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f14,plain,(
% 2.39/0.68    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.39/0.68    inference(flattening,[],[f13])).
% 2.39/0.68  fof(f13,plain,(
% 2.39/0.68    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.39/0.68    inference(ennf_transformation,[],[f11])).
% 2.39/0.68  fof(f11,negated_conjecture,(
% 2.39/0.68    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.39/0.68    inference(negated_conjecture,[],[f10])).
% 2.39/0.68  fof(f10,conjecture,(
% 2.39/0.68    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 2.39/0.68  fof(f111,plain,(
% 2.39/0.68    ( ! [X12,X10,X8,X11,X9] : (~r1_tarski(k2_zfmisc_1(X11,X9),X12) | ~r2_hidden(X10,X11) | r2_hidden(k4_tarski(X10,X8),X12) | ~r2_hidden(X8,X9)) )),
% 2.39/0.68    inference(resolution,[],[f52,f44])).
% 2.39/0.68  fof(f44,plain,(
% 2.39/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f28])).
% 2.39/0.68  fof(f52,plain,(
% 2.39/0.68    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f32])).
% 2.39/0.68  fof(f341,plain,(
% 2.39/0.68    spl7_3 | spl7_4),
% 2.39/0.68    inference(avatar_split_clause,[],[f338,f206,f203])).
% 2.39/0.68  fof(f206,plain,(
% 2.39/0.68    spl7_4 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.39/0.68  fof(f338,plain,(
% 2.39/0.68    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK1) | r2_hidden(X1,sK3)) )),
% 2.39/0.68    inference(resolution,[],[f160,f51])).
% 2.39/0.68  fof(f51,plain,(
% 2.39/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f32])).
% 2.39/0.68  fof(f316,plain,(
% 2.39/0.68    ~spl7_4),
% 2.39/0.68    inference(avatar_contradiction_clause,[],[f315])).
% 2.39/0.68  fof(f315,plain,(
% 2.39/0.68    $false | ~spl7_4),
% 2.39/0.68    inference(subsumption_resolution,[],[f312,f57])).
% 2.39/0.68  fof(f57,plain,(
% 2.39/0.68    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.39/0.68    inference(equality_resolution,[],[f48])).
% 2.39/0.68  fof(f48,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.39/0.68    inference(cnf_transformation,[],[f30])).
% 2.39/0.68  fof(f30,plain,(
% 2.39/0.68    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.39/0.68    inference(flattening,[],[f29])).
% 2.39/0.68  fof(f29,plain,(
% 2.39/0.68    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.39/0.68    inference(nnf_transformation,[],[f9])).
% 2.39/0.68  fof(f9,axiom,(
% 2.39/0.68    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.39/0.68  fof(f312,plain,(
% 2.39/0.68    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | ~spl7_4),
% 2.39/0.68    inference(backward_demodulation,[],[f34,f286])).
% 2.39/0.68  fof(f286,plain,(
% 2.39/0.68    k1_xboole_0 = sK0 | ~spl7_4),
% 2.39/0.68    inference(resolution,[],[f207,f91])).
% 2.39/0.68  fof(f91,plain,(
% 2.39/0.68    ( ! [X3] : (r2_hidden(sK5(X3,k1_xboole_0),X3) | k1_xboole_0 = X3) )),
% 2.39/0.68    inference(resolution,[],[f42,f79])).
% 2.39/0.68  fof(f79,plain,(
% 2.39/0.68    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.39/0.68    inference(forward_demodulation,[],[f78,f67])).
% 2.39/0.68  fof(f67,plain,(
% 2.39/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.39/0.68    inference(forward_demodulation,[],[f53,f38])).
% 2.39/0.68  fof(f38,plain,(
% 2.39/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.39/0.68    inference(cnf_transformation,[],[f5])).
% 2.39/0.68  fof(f5,axiom,(
% 2.39/0.68    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.39/0.68  fof(f53,plain,(
% 2.39/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.39/0.68    inference(definition_unfolding,[],[f37,f39])).
% 2.39/0.68  fof(f39,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.39/0.68    inference(cnf_transformation,[],[f6])).
% 2.39/0.68  fof(f6,axiom,(
% 2.39/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.39/0.68  fof(f37,plain,(
% 2.39/0.68    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f4])).
% 2.39/0.68  fof(f4,axiom,(
% 2.39/0.68    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.39/0.68  fof(f78,plain,(
% 2.39/0.68    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 2.39/0.68    inference(subsumption_resolution,[],[f76,f36])).
% 2.39/0.68  fof(f36,plain,(
% 2.39/0.68    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f7])).
% 2.39/0.68  fof(f7,axiom,(
% 2.39/0.68    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.39/0.68  fof(f76,plain,(
% 2.39/0.68    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 2.39/0.68    inference(superposition,[],[f54,f38])).
% 2.39/0.68  fof(f54,plain,(
% 2.39/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.39/0.68    inference(definition_unfolding,[],[f41,f39])).
% 2.39/0.68  fof(f41,plain,(
% 2.39/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.39/0.68    inference(cnf_transformation,[],[f21])).
% 2.39/0.68  fof(f21,plain,(
% 2.39/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 2.39/0.68  fof(f20,plain,(
% 2.39/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f15,plain,(
% 2.39/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.39/0.68    inference(ennf_transformation,[],[f12])).
% 2.39/0.68  fof(f12,plain,(
% 2.39/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.39/0.68    inference(rectify,[],[f3])).
% 2.39/0.68  fof(f3,axiom,(
% 2.39/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.39/0.68  fof(f42,plain,(
% 2.39/0.68    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | X0 = X1 | r2_hidden(sK5(X0,X1),X0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f24])).
% 2.39/0.68  fof(f24,plain,(
% 2.39/0.68    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 2.39/0.68  fof(f23,plain,(
% 2.39/0.68    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f22,plain,(
% 2.39/0.68    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.39/0.68    inference(nnf_transformation,[],[f16])).
% 2.39/0.68  fof(f16,plain,(
% 2.39/0.68    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.39/0.68    inference(ennf_transformation,[],[f2])).
% 2.39/0.68  fof(f2,axiom,(
% 2.39/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.39/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.39/0.68  fof(f207,plain,(
% 2.39/0.68    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl7_4),
% 2.39/0.68    inference(avatar_component_clause,[],[f206])).
% 2.39/0.68  fof(f34,plain,(
% 2.39/0.68    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 2.39/0.68    inference(cnf_transformation,[],[f19])).
% 2.39/0.68  fof(f250,plain,(
% 2.39/0.68    ~spl7_5),
% 2.39/0.68    inference(avatar_contradiction_clause,[],[f249])).
% 2.39/0.68  fof(f249,plain,(
% 2.39/0.68    $false | ~spl7_5),
% 2.39/0.68    inference(subsumption_resolution,[],[f246,f56])).
% 2.39/0.68  fof(f56,plain,(
% 2.39/0.68    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.39/0.68    inference(equality_resolution,[],[f49])).
% 2.39/0.68  fof(f49,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.39/0.68    inference(cnf_transformation,[],[f30])).
% 2.39/0.68  fof(f246,plain,(
% 2.39/0.68    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | ~spl7_5),
% 2.39/0.68    inference(backward_demodulation,[],[f34,f219])).
% 2.39/0.68  fof(f219,plain,(
% 2.39/0.68    k1_xboole_0 = sK1 | ~spl7_5),
% 2.39/0.68    inference(resolution,[],[f211,f91])).
% 2.39/0.68  fof(f211,plain,(
% 2.39/0.68    ( ! [X3] : (~r2_hidden(X3,sK1)) ) | ~spl7_5),
% 2.39/0.68    inference(avatar_component_clause,[],[f210])).
% 2.39/0.68  fof(f66,plain,(
% 2.39/0.68    ~spl7_1 | ~spl7_2),
% 2.39/0.68    inference(avatar_split_clause,[],[f35,f63,f59])).
% 2.39/0.68  fof(f35,plain,(
% 2.39/0.68    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 2.39/0.68    inference(cnf_transformation,[],[f19])).
% 2.39/0.68  % SZS output end Proof for theBenchmark
% 2.39/0.68  % (3692)------------------------------
% 2.39/0.68  % (3692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.68  % (3692)Termination reason: Refutation
% 2.39/0.68  
% 2.39/0.68  % (3692)Memory used [KB]: 6396
% 2.39/0.68  % (3692)Time elapsed: 0.241 s
% 2.39/0.68  % (3692)------------------------------
% 2.39/0.68  % (3692)------------------------------
% 2.39/0.68  % (3680)Success in time 0.314 s
%------------------------------------------------------------------------------
