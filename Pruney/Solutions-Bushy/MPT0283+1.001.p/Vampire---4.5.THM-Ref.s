%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0283+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 4.03s
% Output     : Refutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 180 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  460 ( 729 expanded)
%              Number of equality atoms :   70 (  96 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f105,f110,f344,f352,f358,f815,f841,f846,f858,f903,f917,f919])).

fof(f919,plain,
    ( ~ spl7_3
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f918])).

fof(f918,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f109,f916])).

fof(f916,plain,
    ( ! [X2] : ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(X2,sK1))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f915])).

fof(f915,plain,
    ( spl7_34
  <=> ! [X2] : ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(X2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f109,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_3
  <=> r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f917,plain,
    ( spl7_4
    | spl7_34
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f908,f856,f915,f245])).

fof(f245,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f856,plain,
    ( spl7_31
  <=> r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f908,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(X2,sK1))
        | k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) )
    | ~ spl7_31 ),
    inference(resolution,[],[f857,f213])).

fof(f213,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,k4_xboole_0(X4,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f202,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f121,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = k3_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f857,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f856])).

fof(f903,plain,
    ( ~ spl7_3
    | spl7_29 ),
    inference(avatar_contradiction_clause,[],[f902])).

fof(f902,plain,
    ( $false
    | ~ spl7_3
    | spl7_29 ),
    inference(subsumption_resolution,[],[f109,f899])).

fof(f899,plain,
    ( ! [X3] : ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,X3))
    | spl7_29 ),
    inference(resolution,[],[f859,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f859,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),X0) )
    | spl7_29 ),
    inference(resolution,[],[f845,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f845,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK0)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f844])).

fof(f844,plain,
    ( spl7_29
  <=> r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f858,plain,
    ( spl7_31
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f853,f839,f856])).

fof(f839,plain,
    ( spl7_28
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f853,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f840,f83])).

fof(f83,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f840,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f839])).

fof(f846,plain,
    ( ~ spl7_29
    | spl7_27 ),
    inference(avatar_split_clause,[],[f842,f836,f844])).

fof(f836,plain,
    ( spl7_27
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f842,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),sK0)
    | spl7_27 ),
    inference(resolution,[],[f837,f82])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f837,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f836])).

fof(f841,plain,
    ( ~ spl7_27
    | spl7_28
    | spl7_26 ),
    inference(avatar_split_clause,[],[f834,f813,f839,f836])).

fof(f813,plain,
    ( spl7_26
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f834,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(sK0))
    | spl7_26 ),
    inference(resolution,[],[f814,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f814,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f813])).

fof(f815,plain,
    ( ~ spl7_26
    | spl7_1 ),
    inference(avatar_split_clause,[],[f785,f91,f813])).

fof(f91,plain,
    ( spl7_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f785,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))
    | spl7_1 ),
    inference(resolution,[],[f112,f92])).

fof(f92,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r2_hidden(sK2(X0,k2_xboole_0(X1,X2)),X2) ) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f358,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f351,f80])).

fof(f80,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f351,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl7_17
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f352,plain,
    ( ~ spl7_17
    | spl7_16 ),
    inference(avatar_split_clause,[],[f347,f338,f350])).

fof(f338,plain,
    ( spl7_16
  <=> r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f347,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | spl7_16 ),
    inference(resolution,[],[f343,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f343,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f338])).

fof(f344,plain,
    ( spl7_1
    | ~ spl7_16
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f328,f245,f338,f91])).

fof(f328,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_4 ),
    inference(superposition,[],[f56,f246])).

fof(f246,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f245])).

fof(f110,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f106,f103,f108])).

fof(f103,plain,
    ( spl7_2
  <=> r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f106,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k4_xboole_0(sK0,sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f104,f83])).

fof(f104,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl7_2
    | spl7_1 ),
    inference(avatar_split_clause,[],[f101,f91,f103])).

fof(f101,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | spl7_1 ),
    inference(resolution,[],[f55,f92])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f47,f91])).

fof(f47,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))))
   => ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X0,X1)),k2_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_zfmisc_1)).

%------------------------------------------------------------------------------
