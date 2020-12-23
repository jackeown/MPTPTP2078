%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0305+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  165 ( 368 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2874,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1808,f2348,f2522,f2749,f2873])).

fof(f2873,plain,(
    ~ spl52_14 ),
    inference(avatar_contradiction_clause,[],[f2872])).

fof(f2872,plain,
    ( $false
    | ~ spl52_14 ),
    inference(subsumption_resolution,[],[f2871,f772])).

fof(f772,plain,(
    ~ r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f604])).

fof(f604,plain,
    ( ~ r1_tarski(sK5,sK6)
    & ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK6))
      | r1_tarski(k2_zfmisc_1(sK5,sK4),k2_zfmisc_1(sK6,sK4)) )
    & k1_xboole_0 != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f414,f603])).

fof(f603,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK5,sK6)
      & ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK6))
        | r1_tarski(k2_zfmisc_1(sK5,sK4),k2_zfmisc_1(sK6,sK4)) )
      & k1_xboole_0 != sK4 ) ),
    introduced(choice_axiom,[])).

fof(f414,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f326])).

fof(f326,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f325])).

fof(f325,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f2871,plain,
    ( r1_tarski(sK5,sK6)
    | ~ spl52_14 ),
    inference(duplicate_literal_removal,[],[f2867])).

fof(f2867,plain,
    ( r1_tarski(sK5,sK6)
    | r1_tarski(sK5,sK6)
    | ~ spl52_14 ),
    inference(resolution,[],[f2758,f943])).

fof(f943,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK16(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f635])).

fof(f635,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK16(X0,X1),X1)
          & r2_hidden(sK16(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f633,f634])).

fof(f634,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK16(X0,X1),X1)
        & r2_hidden(sK16(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f632])).

fof(f632,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f470])).

fof(f470,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2758,plain,
    ( ! [X3] :
        ( r2_hidden(sK16(sK5,X3),sK6)
        | r1_tarski(sK5,X3) )
    | ~ spl52_14 ),
    inference(resolution,[],[f2347,f942])).

fof(f942,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK16(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f635])).

fof(f2347,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK6) )
    | ~ spl52_14 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2346,plain,
    ( spl52_14
  <=> ! [X2] :
        ( ~ r2_hidden(X2,sK5)
        | r2_hidden(X2,sK6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_14])])).

fof(f2749,plain,
    ( spl52_14
    | spl52_13
    | ~ spl52_1 ),
    inference(avatar_split_clause,[],[f2740,f1801,f2343,f2346])).

fof(f2343,plain,
    ( spl52_13
  <=> ! [X3] : ~ r2_hidden(X3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_13])])).

fof(f1801,plain,
    ( spl52_1
  <=> r1_tarski(k2_zfmisc_1(sK5,sK4),k2_zfmisc_1(sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_1])])).

fof(f2740,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK4)
        | ~ r2_hidden(X1,sK5)
        | r2_hidden(X1,sK6) )
    | ~ spl52_1 ),
    inference(resolution,[],[f2575,f1253])).

fof(f1253,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f742])).

fof(f742,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f311])).

fof(f311,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f2575,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK4))
        | ~ r2_hidden(X1,sK4)
        | ~ r2_hidden(X0,sK5) )
    | ~ spl52_1 ),
    inference(resolution,[],[f2561,f1255])).

fof(f1255,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f2561,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK5,sK4))
        | r2_hidden(X0,k2_zfmisc_1(sK6,sK4)) )
    | ~ spl52_1 ),
    inference(resolution,[],[f1803,f941])).

fof(f941,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f635])).

fof(f1803,plain,
    ( r1_tarski(k2_zfmisc_1(sK5,sK4),k2_zfmisc_1(sK6,sK4))
    | ~ spl52_1 ),
    inference(avatar_component_clause,[],[f1801])).

fof(f2522,plain,(
    ~ spl52_13 ),
    inference(avatar_contradiction_clause,[],[f2521])).

fof(f2521,plain,
    ( $false
    | ~ spl52_13 ),
    inference(subsumption_resolution,[],[f2495,f1446])).

fof(f1446,plain,(
    ~ sQ51_eqProxy(k1_xboole_0,sK4) ),
    inference(equality_proxy_replacement,[],[f770,f1430])).

fof(f1430,plain,(
    ! [X1,X0] :
      ( sQ51_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ51_eqProxy])])).

fof(f770,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f604])).

fof(f2495,plain,
    ( sQ51_eqProxy(k1_xboole_0,sK4)
    | ~ spl52_13 ),
    inference(resolution,[],[f2344,f1470])).

fof(f1470,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | sQ51_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f810,f1430])).

fof(f810,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f610])).

fof(f610,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f421,f609])).

fof(f609,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f421,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2344,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK4)
    | ~ spl52_13 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f2348,plain,
    ( spl52_13
    | spl52_14
    | ~ spl52_2 ),
    inference(avatar_split_clause,[],[f2334,f1805,f2346,f2343])).

fof(f1805,plain,
    ( spl52_2
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl52_2])])).

fof(f2334,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK5)
        | ~ r2_hidden(X3,sK4)
        | r2_hidden(X2,sK6) )
    | ~ spl52_2 ),
    inference(resolution,[],[f2138,f1254])).

fof(f1254,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f2138,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK6))
        | ~ r2_hidden(X1,sK5)
        | ~ r2_hidden(X0,sK4) )
    | ~ spl52_2 ),
    inference(resolution,[],[f2122,f1255])).

fof(f2122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(sK4,sK5))
        | r2_hidden(X0,k2_zfmisc_1(sK4,sK6)) )
    | ~ spl52_2 ),
    inference(resolution,[],[f1807,f941])).

fof(f1807,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK6))
    | ~ spl52_2 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f1808,plain,
    ( spl52_1
    | spl52_2 ),
    inference(avatar_split_clause,[],[f771,f1805,f1801])).

fof(f771,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK6))
    | r1_tarski(k2_zfmisc_1(sK5,sK4),k2_zfmisc_1(sK6,sK4)) ),
    inference(cnf_transformation,[],[f604])).
%------------------------------------------------------------------------------
