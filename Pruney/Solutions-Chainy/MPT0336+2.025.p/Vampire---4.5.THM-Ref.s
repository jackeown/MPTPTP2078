%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:26 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 333 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  380 ( 972 expanded)
%              Number of equality atoms :   75 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f115,f404,f449,f460,f479,f483,f580,f637,f678])).

fof(f678,plain,
    ( spl7_1
    | ~ spl7_5
    | ~ spl7_47
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f664,f402,f635,f113,f89])).

fof(f89,plain,
    ( spl7_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f113,plain,
    ( spl7_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f635,plain,
    ( spl7_47
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f402,plain,
    ( spl7_28
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f664,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f659,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f659,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),X8)
        | ~ r1_xboole_0(X8,sK0)
        | ~ r1_xboole_0(X8,sK2) )
    | ~ spl7_28 ),
    inference(resolution,[],[f268,f403])).

fof(f403,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f402])).

fof(f268,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r2_hidden(X12,k2_xboole_0(X10,X11))
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10)
      | ~ r2_hidden(X12,X9) ) ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f637,plain,
    ( spl7_47
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f633,f578,f635])).

fof(f578,plain,
    ( spl7_46
  <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f633,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl7_46 ),
    inference(trivial_inequality_removal,[],[f632])).

fof(f632,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0)
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f631,f220])).

fof(f220,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(resolution,[],[f215,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f215,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f190,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f190,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f82,f44])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f631,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))
    | r1_xboole_0(sK1,sK0)
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f623,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f50,f50])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f623,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))
    | r1_xboole_0(sK1,sK0)
    | ~ spl7_46 ),
    inference(superposition,[],[f76,f579])).

fof(f579,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f578])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f580,plain,
    ( spl7_46
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f576,f458,f578])).

fof(f458,plain,
    ( spl7_33
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f576,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f560,f275])).

fof(f275,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f150])).

fof(f150,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f77,f44])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f560,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl7_33 ),
    inference(superposition,[],[f320,f459])).

fof(f459,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f458])).

fof(f320,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f73,f75])).

fof(f483,plain,(
    spl7_36 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | spl7_36 ),
    inference(resolution,[],[f478,f326])).

fof(f326,plain,(
    ! [X12,X11] : r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11) ),
    inference(superposition,[],[f46,f75])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f478,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl7_36 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl7_36
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f479,plain,
    ( ~ spl7_3
    | ~ spl7_36
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f466,f447,f93,f477,f97])).

fof(f97,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f93,plain,
    ( spl7_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f447,plain,
    ( spl7_32
  <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f466,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK3,sK2)
    | ~ spl7_2
    | ~ spl7_32 ),
    inference(resolution,[],[f461,f105])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f53,f94])).

fof(f94,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f461,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,X0)
        | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f448,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f448,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f447])).

fof(f460,plain,
    ( spl7_33
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f455,f444,f458])).

fof(f444,plain,
    ( spl7_31
  <=> ! [X2] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f455,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl7_31 ),
    inference(resolution,[],[f445,f222])).

fof(f222,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f217,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f217,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f190,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f445,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f444])).

fof(f449,plain,
    ( spl7_31
    | spl7_32
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f441,f101,f447,f444])).

fof(f101,plain,
    ( spl7_4
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f441,plain,
    ( ! [X2] :
        ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f440])).

fof(f440,plain,
    ( ! [X2] :
        ( r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2) )
    | ~ spl7_4 ),
    inference(superposition,[],[f58,f436])).

fof(f436,plain,
    ( ! [X0] :
        ( sK3 = sK5(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f428,f87])).

fof(f87,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f428,plain,
    ( ! [X5] :
        ( r2_hidden(sK5(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5),k2_enumset1(sK3,sK3,sK3,sK3))
        | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5) )
    | ~ spl7_4 ),
    inference(resolution,[],[f146,f102])).

fof(f102,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f146,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tarski(X9,X11)
      | r2_hidden(sK5(X9,X10),X11)
      | r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f57,f58])).

fof(f404,plain,
    ( spl7_28
    | spl7_1 ),
    inference(avatar_split_clause,[],[f399,f89,f402])).

fof(f399,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2))
    | spl7_1 ),
    inference(resolution,[],[f393,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_xboole_0(sK0,sK2),X0)
        | r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),X0) )
    | spl7_1 ),
    inference(resolution,[],[f144,f90])).

fof(f90,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f144,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X3,X4)
      | ~ r1_tarski(X3,X5)
      | r2_hidden(sK4(X3,X4),X5) ) ),
    inference(resolution,[],[f57,f51])).

fof(f115,plain,
    ( spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f111,f93,f113])).

fof(f111,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f107,f52])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1,X0),sK2)
        | r1_xboole_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f105,f51])).

fof(f103,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f74,f101])).

fof(f74,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f40,f50,f72])).

fof(f40,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f99,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (29503)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29513)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29493)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29494)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.52  % (29492)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (29495)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.54  % (29489)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.54  % (29491)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (29517)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.55  % (29518)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.55  % (29498)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.55  % (29519)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.55  % (29516)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.55  % (29511)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.55  % (29505)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (29512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.55  % (29507)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (29509)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.55  % (29510)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.55  % (29508)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.55  % (29490)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.56  % (29496)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.56  % (29497)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.56  % (29502)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.56  % (29500)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.56  % (29499)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.56  % (29501)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.56  % (29514)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.57  % (29515)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.57  % (29506)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.58  % (29509)Refutation found. Thanks to Tanya!
% 1.33/0.58  % SZS status Theorem for theBenchmark
% 1.33/0.58  % SZS output start Proof for theBenchmark
% 1.33/0.58  fof(f686,plain,(
% 1.33/0.58    $false),
% 1.33/0.58    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f115,f404,f449,f460,f479,f483,f580,f637,f678])).
% 1.33/0.58  fof(f678,plain,(
% 1.33/0.58    spl7_1 | ~spl7_5 | ~spl7_47 | ~spl7_28),
% 1.33/0.58    inference(avatar_split_clause,[],[f664,f402,f635,f113,f89])).
% 1.33/0.58  fof(f89,plain,(
% 1.33/0.58    spl7_1 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.33/0.58  fof(f113,plain,(
% 1.33/0.58    spl7_5 <=> r1_xboole_0(sK1,sK2)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.33/0.58  fof(f635,plain,(
% 1.33/0.58    spl7_47 <=> r1_xboole_0(sK1,sK0)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.33/0.58  fof(f402,plain,(
% 1.33/0.58    spl7_28 <=> r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2))),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.33/0.58  fof(f664,plain,(
% 1.33/0.58    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2) | r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl7_28),
% 1.33/0.58    inference(resolution,[],[f659,f52])).
% 1.33/0.58  fof(f52,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f28])).
% 1.33/0.58  fof(f28,plain,(
% 1.33/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.33/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).
% 1.33/0.58  fof(f27,plain,(
% 1.33/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.33/0.58    introduced(choice_axiom,[])).
% 1.33/0.58  fof(f21,plain,(
% 1.33/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.33/0.58    inference(ennf_transformation,[],[f18])).
% 1.33/0.58  fof(f18,plain,(
% 1.33/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.58    inference(rectify,[],[f4])).
% 1.33/0.58  fof(f4,axiom,(
% 1.33/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.33/0.58  fof(f659,plain,(
% 1.33/0.58    ( ! [X8] : (~r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),X8) | ~r1_xboole_0(X8,sK0) | ~r1_xboole_0(X8,sK2)) ) | ~spl7_28),
% 1.33/0.58    inference(resolution,[],[f268,f403])).
% 1.33/0.58  fof(f403,plain,(
% 1.33/0.58    r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2)) | ~spl7_28),
% 1.33/0.58    inference(avatar_component_clause,[],[f402])).
% 1.33/0.58  fof(f268,plain,(
% 1.33/0.58    ( ! [X12,X10,X11,X9] : (~r2_hidden(X12,k2_xboole_0(X10,X11)) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10) | ~r2_hidden(X12,X9)) )),
% 1.33/0.58    inference(resolution,[],[f68,f53])).
% 1.33/0.58  fof(f53,plain,(
% 1.33/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f28])).
% 1.33/0.58  fof(f68,plain,(
% 1.33/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f24])).
% 1.33/0.58  fof(f24,plain,(
% 1.33/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.33/0.58    inference(ennf_transformation,[],[f10])).
% 1.33/0.58  fof(f10,axiom,(
% 1.33/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.33/0.58  fof(f637,plain,(
% 1.33/0.58    spl7_47 | ~spl7_46),
% 1.33/0.58    inference(avatar_split_clause,[],[f633,f578,f635])).
% 1.33/0.58  fof(f578,plain,(
% 1.33/0.58    spl7_46 <=> k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.33/0.58  fof(f633,plain,(
% 1.33/0.58    r1_xboole_0(sK1,sK0) | ~spl7_46),
% 1.33/0.58    inference(trivial_inequality_removal,[],[f632])).
% 1.33/0.58  fof(f632,plain,(
% 1.33/0.58    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0) | ~spl7_46),
% 1.33/0.58    inference(forward_demodulation,[],[f631,f220])).
% 1.33/0.58  fof(f220,plain,(
% 1.33/0.58    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 1.33/0.58    inference(resolution,[],[f215,f77])).
% 1.33/0.58  fof(f77,plain,(
% 1.33/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.33/0.58    inference(definition_unfolding,[],[f60,f50])).
% 1.33/0.58  fof(f50,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.33/0.58    inference(cnf_transformation,[],[f8])).
% 1.33/0.58  fof(f8,axiom,(
% 1.33/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.33/0.58  fof(f60,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f35])).
% 1.33/0.58  fof(f35,plain,(
% 1.33/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.33/0.58    inference(nnf_transformation,[],[f3])).
% 1.33/0.58  fof(f3,axiom,(
% 1.33/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.33/0.58  fof(f215,plain,(
% 1.33/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.58    inference(resolution,[],[f190,f51])).
% 1.33/0.58  fof(f51,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f28])).
% 1.33/0.58  fof(f190,plain,(
% 1.33/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.33/0.58    inference(resolution,[],[f82,f44])).
% 1.33/0.58  fof(f44,plain,(
% 1.33/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f9])).
% 1.33/0.58  fof(f9,axiom,(
% 1.33/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.33/0.58  fof(f82,plain,(
% 1.33/0.58    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.58    inference(definition_unfolding,[],[f66,f72])).
% 1.33/0.58  fof(f72,plain,(
% 1.33/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.33/0.58    inference(definition_unfolding,[],[f45,f71])).
% 1.33/0.58  fof(f71,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.33/0.58    inference(definition_unfolding,[],[f48,f67])).
% 1.33/0.58  fof(f67,plain,(
% 1.33/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f14])).
% 1.33/0.58  fof(f14,axiom,(
% 1.33/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.33/0.58  fof(f48,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f13])).
% 1.33/0.58  fof(f13,axiom,(
% 1.33/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.58  fof(f45,plain,(
% 1.33/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f12])).
% 1.33/0.58  fof(f12,axiom,(
% 1.33/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.58  fof(f66,plain,(
% 1.33/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f23])).
% 1.33/0.58  fof(f23,plain,(
% 1.33/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.33/0.58    inference(ennf_transformation,[],[f15])).
% 1.33/0.58  fof(f15,axiom,(
% 1.33/0.58    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.33/0.58  fof(f631,plain,(
% 1.33/0.58    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) | r1_xboole_0(sK1,sK0) | ~spl7_46),
% 1.33/0.58    inference(forward_demodulation,[],[f623,f75])).
% 1.33/0.58  fof(f75,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.33/0.58    inference(definition_unfolding,[],[f47,f50,f50])).
% 1.33/0.58  fof(f47,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f1])).
% 1.33/0.58  fof(f1,axiom,(
% 1.33/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.33/0.58  fof(f623,plain,(
% 1.33/0.58    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) | r1_xboole_0(sK1,sK0) | ~spl7_46),
% 1.33/0.58    inference(superposition,[],[f76,f579])).
% 1.33/0.58  fof(f579,plain,(
% 1.33/0.58    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) | ~spl7_46),
% 1.33/0.58    inference(avatar_component_clause,[],[f578])).
% 1.33/0.58  fof(f76,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.33/0.58    inference(definition_unfolding,[],[f61,f50])).
% 1.33/0.58  fof(f61,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.33/0.58    inference(cnf_transformation,[],[f35])).
% 1.33/0.58  fof(f580,plain,(
% 1.33/0.58    spl7_46 | ~spl7_33),
% 1.33/0.58    inference(avatar_split_clause,[],[f576,f458,f578])).
% 1.33/0.58  fof(f458,plain,(
% 1.33/0.58    spl7_33 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 1.33/0.58  fof(f576,plain,(
% 1.33/0.58    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) | ~spl7_33),
% 1.33/0.58    inference(forward_demodulation,[],[f560,f275])).
% 1.33/0.58  fof(f275,plain,(
% 1.33/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.33/0.58    inference(superposition,[],[f73,f150])).
% 1.33/0.58  fof(f150,plain,(
% 1.33/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.33/0.58    inference(resolution,[],[f77,f44])).
% 1.33/0.58  fof(f73,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.33/0.58    inference(definition_unfolding,[],[f49,f50])).
% 1.33/0.58  fof(f49,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.58    inference(cnf_transformation,[],[f6])).
% 1.33/0.58  fof(f6,axiom,(
% 1.33/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.58  fof(f560,plain,(
% 1.33/0.58    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0) | ~spl7_33),
% 1.33/0.58    inference(superposition,[],[f320,f459])).
% 1.33/0.58  fof(f459,plain,(
% 1.33/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl7_33),
% 1.33/0.58    inference(avatar_component_clause,[],[f458])).
% 1.33/0.58  fof(f320,plain,(
% 1.33/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.33/0.58    inference(superposition,[],[f73,f75])).
% 1.33/0.58  fof(f483,plain,(
% 1.33/0.58    spl7_36),
% 1.33/0.58    inference(avatar_contradiction_clause,[],[f481])).
% 1.33/0.58  fof(f481,plain,(
% 1.33/0.58    $false | spl7_36),
% 1.33/0.58    inference(resolution,[],[f478,f326])).
% 1.33/0.58  fof(f326,plain,(
% 1.33/0.58    ( ! [X12,X11] : (r1_tarski(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) )),
% 1.33/0.58    inference(superposition,[],[f46,f75])).
% 1.33/0.58  fof(f46,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f7])).
% 1.33/0.58  fof(f7,axiom,(
% 1.33/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.33/0.58  fof(f478,plain,(
% 1.33/0.58    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl7_36),
% 1.33/0.58    inference(avatar_component_clause,[],[f477])).
% 1.33/0.58  fof(f477,plain,(
% 1.33/0.58    spl7_36 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 1.33/0.58  fof(f479,plain,(
% 1.33/0.58    ~spl7_3 | ~spl7_36 | ~spl7_2 | ~spl7_32),
% 1.33/0.58    inference(avatar_split_clause,[],[f466,f447,f93,f477,f97])).
% 1.33/0.58  fof(f97,plain,(
% 1.33/0.58    spl7_3 <=> r2_hidden(sK3,sK2)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.33/0.58  fof(f93,plain,(
% 1.33/0.58    spl7_2 <=> r1_xboole_0(sK2,sK1)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.33/0.58  fof(f447,plain,(
% 1.33/0.58    spl7_32 <=> r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.33/0.58  fof(f466,plain,(
% 1.33/0.58    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK3,sK2) | (~spl7_2 | ~spl7_32)),
% 1.33/0.58    inference(resolution,[],[f461,f105])).
% 1.33/0.58  fof(f105,plain,(
% 1.33/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2)) ) | ~spl7_2),
% 1.33/0.58    inference(resolution,[],[f53,f94])).
% 1.33/0.58  fof(f94,plain,(
% 1.33/0.58    r1_xboole_0(sK2,sK1) | ~spl7_2),
% 1.33/0.58    inference(avatar_component_clause,[],[f93])).
% 1.33/0.58  fof(f461,plain,(
% 1.33/0.58    ( ! [X0] : (r2_hidden(sK3,X0) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)) ) | ~spl7_32),
% 1.33/0.58    inference(resolution,[],[f448,f57])).
% 1.33/0.58  fof(f57,plain,(
% 1.33/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f34])).
% 1.33/0.58  fof(f34,plain,(
% 1.33/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.33/0.58  fof(f33,plain,(
% 1.33/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.33/0.58    introduced(choice_axiom,[])).
% 1.33/0.58  fof(f32,plain,(
% 1.33/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.58    inference(rectify,[],[f31])).
% 1.33/0.58  fof(f31,plain,(
% 1.33/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.58    inference(nnf_transformation,[],[f22])).
% 1.33/0.58  fof(f22,plain,(
% 1.33/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.58    inference(ennf_transformation,[],[f2])).
% 1.33/0.58  fof(f2,axiom,(
% 1.33/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.58  fof(f448,plain,(
% 1.33/0.58    r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl7_32),
% 1.33/0.58    inference(avatar_component_clause,[],[f447])).
% 1.33/0.58  fof(f460,plain,(
% 1.33/0.58    spl7_33 | ~spl7_31),
% 1.33/0.58    inference(avatar_split_clause,[],[f455,f444,f458])).
% 1.33/0.58  fof(f444,plain,(
% 1.33/0.58    spl7_31 <=> ! [X2] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.33/0.58  fof(f455,plain,(
% 1.33/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl7_31),
% 1.33/0.58    inference(resolution,[],[f445,f222])).
% 1.33/0.58  fof(f222,plain,(
% 1.33/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.33/0.58    inference(resolution,[],[f217,f56])).
% 1.33/0.58  fof(f56,plain,(
% 1.33/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f30])).
% 1.33/0.58  fof(f30,plain,(
% 1.33/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.58    inference(flattening,[],[f29])).
% 1.33/0.58  fof(f29,plain,(
% 1.33/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.58    inference(nnf_transformation,[],[f5])).
% 1.33/0.58  fof(f5,axiom,(
% 1.33/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.58  fof(f217,plain,(
% 1.33/0.58    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.33/0.58    inference(resolution,[],[f190,f58])).
% 1.33/0.58  fof(f58,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.33/0.58    inference(cnf_transformation,[],[f34])).
% 1.33/0.58  fof(f445,plain,(
% 1.33/0.58    ( ! [X2] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)) ) | ~spl7_31),
% 1.33/0.58    inference(avatar_component_clause,[],[f444])).
% 1.33/0.58  fof(f449,plain,(
% 1.33/0.58    spl7_31 | spl7_32 | ~spl7_4),
% 1.33/0.58    inference(avatar_split_clause,[],[f441,f101,f447,f444])).
% 1.33/0.58  fof(f101,plain,(
% 1.33/0.58    spl7_4 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.33/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.33/0.58  fof(f441,plain,(
% 1.33/0.58    ( ! [X2] : (r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)) ) | ~spl7_4),
% 1.33/0.58    inference(duplicate_literal_removal,[],[f440])).
% 1.33/0.58  fof(f440,plain,(
% 1.33/0.58    ( ! [X2] : (r2_hidden(sK3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X2)) ) | ~spl7_4),
% 1.33/0.58    inference(superposition,[],[f58,f436])).
% 1.33/0.58  fof(f436,plain,(
% 1.33/0.58    ( ! [X0] : (sK3 = sK5(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)) ) | ~spl7_4),
% 1.33/0.58    inference(resolution,[],[f428,f87])).
% 1.33/0.58  fof(f87,plain,(
% 1.33/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.33/0.58    inference(equality_resolution,[],[f81])).
% 1.33/0.58  fof(f81,plain,(
% 1.33/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.33/0.58    inference(definition_unfolding,[],[f62,f72])).
% 1.33/0.58  fof(f62,plain,(
% 1.33/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.33/0.58    inference(cnf_transformation,[],[f39])).
% 1.33/0.58  fof(f39,plain,(
% 1.33/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 1.33/0.58  fof(f38,plain,(
% 1.33/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.33/0.58    introduced(choice_axiom,[])).
% 1.33/0.58  fof(f37,plain,(
% 1.33/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.58    inference(rectify,[],[f36])).
% 1.33/0.58  fof(f36,plain,(
% 1.33/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.33/0.58    inference(nnf_transformation,[],[f11])).
% 1.33/0.58  fof(f11,axiom,(
% 1.33/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.33/0.58  fof(f428,plain,(
% 1.33/0.58    ( ! [X5] : (r2_hidden(sK5(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5),k2_enumset1(sK3,sK3,sK3,sK3)) | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X5)) ) | ~spl7_4),
% 1.33/0.58    inference(resolution,[],[f146,f102])).
% 1.33/0.58  fof(f102,plain,(
% 1.33/0.58    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl7_4),
% 1.33/0.58    inference(avatar_component_clause,[],[f101])).
% 1.33/0.58  fof(f146,plain,(
% 1.33/0.58    ( ! [X10,X11,X9] : (~r1_tarski(X9,X11) | r2_hidden(sK5(X9,X10),X11) | r1_tarski(X9,X10)) )),
% 1.33/0.58    inference(resolution,[],[f57,f58])).
% 1.33/0.58  fof(f404,plain,(
% 1.33/0.58    spl7_28 | spl7_1),
% 1.33/0.58    inference(avatar_split_clause,[],[f399,f89,f402])).
% 1.33/0.58  fof(f399,plain,(
% 1.33/0.58    r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK0,sK2)) | spl7_1),
% 1.33/0.58    inference(resolution,[],[f393,f83])).
% 1.33/0.58  fof(f83,plain,(
% 1.33/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.58    inference(equality_resolution,[],[f55])).
% 1.33/0.58  fof(f55,plain,(
% 1.33/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.58    inference(cnf_transformation,[],[f30])).
% 1.33/0.58  fof(f393,plain,(
% 1.33/0.58    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,sK2),X0) | r2_hidden(sK4(k2_xboole_0(sK0,sK2),sK1),X0)) ) | spl7_1),
% 1.33/0.58    inference(resolution,[],[f144,f90])).
% 1.33/0.58  fof(f90,plain,(
% 1.33/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl7_1),
% 1.33/0.58    inference(avatar_component_clause,[],[f89])).
% 1.33/0.58  fof(f144,plain,(
% 1.33/0.58    ( ! [X4,X5,X3] : (r1_xboole_0(X3,X4) | ~r1_tarski(X3,X5) | r2_hidden(sK4(X3,X4),X5)) )),
% 1.33/0.58    inference(resolution,[],[f57,f51])).
% 1.33/0.58  fof(f115,plain,(
% 1.33/0.58    spl7_5 | ~spl7_2),
% 1.33/0.58    inference(avatar_split_clause,[],[f111,f93,f113])).
% 1.33/0.58  fof(f111,plain,(
% 1.33/0.58    r1_xboole_0(sK1,sK2) | ~spl7_2),
% 1.33/0.58    inference(duplicate_literal_removal,[],[f110])).
% 1.33/0.58  fof(f110,plain,(
% 1.33/0.58    r1_xboole_0(sK1,sK2) | r1_xboole_0(sK1,sK2) | ~spl7_2),
% 1.33/0.58    inference(resolution,[],[f107,f52])).
% 1.33/0.58  fof(f107,plain,(
% 1.33/0.58    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK2) | r1_xboole_0(sK1,X0)) ) | ~spl7_2),
% 1.33/0.58    inference(resolution,[],[f105,f51])).
% 1.33/0.58  fof(f103,plain,(
% 1.33/0.58    spl7_4),
% 1.33/0.58    inference(avatar_split_clause,[],[f74,f101])).
% 1.33/0.58  fof(f74,plain,(
% 1.33/0.58    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.33/0.58    inference(definition_unfolding,[],[f40,f50,f72])).
% 1.33/0.58  fof(f40,plain,(
% 1.33/0.58    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.33/0.58    inference(cnf_transformation,[],[f26])).
% 1.33/0.58  fof(f26,plain,(
% 1.33/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.33/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f25])).
% 1.33/0.58  fof(f25,plain,(
% 1.33/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.33/0.58    introduced(choice_axiom,[])).
% 1.33/0.58  fof(f20,plain,(
% 1.33/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.33/0.58    inference(flattening,[],[f19])).
% 1.33/0.58  fof(f19,plain,(
% 1.33/0.58    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.33/0.58    inference(ennf_transformation,[],[f17])).
% 1.33/0.58  fof(f17,negated_conjecture,(
% 1.33/0.58    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.33/0.58    inference(negated_conjecture,[],[f16])).
% 1.33/0.58  fof(f16,conjecture,(
% 1.33/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.33/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.33/0.58  fof(f99,plain,(
% 1.33/0.58    spl7_3),
% 1.33/0.58    inference(avatar_split_clause,[],[f41,f97])).
% 1.33/0.58  fof(f41,plain,(
% 1.33/0.58    r2_hidden(sK3,sK2)),
% 1.33/0.58    inference(cnf_transformation,[],[f26])).
% 1.33/0.58  fof(f95,plain,(
% 1.33/0.58    spl7_2),
% 1.33/0.58    inference(avatar_split_clause,[],[f42,f93])).
% 1.33/0.58  fof(f42,plain,(
% 1.33/0.58    r1_xboole_0(sK2,sK1)),
% 1.33/0.58    inference(cnf_transformation,[],[f26])).
% 1.33/0.58  fof(f91,plain,(
% 1.33/0.58    ~spl7_1),
% 1.33/0.58    inference(avatar_split_clause,[],[f43,f89])).
% 1.33/0.58  fof(f43,plain,(
% 1.33/0.58    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.33/0.58    inference(cnf_transformation,[],[f26])).
% 1.33/0.58  % SZS output end Proof for theBenchmark
% 1.33/0.58  % (29509)------------------------------
% 1.33/0.58  % (29509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.58  % (29509)Termination reason: Refutation
% 1.33/0.58  
% 1.33/0.58  % (29509)Memory used [KB]: 11129
% 1.33/0.58  % (29509)Time elapsed: 0.173 s
% 1.33/0.58  % (29509)------------------------------
% 1.33/0.58  % (29509)------------------------------
% 1.33/0.61  % (29487)Success in time 0.241 s
%------------------------------------------------------------------------------
