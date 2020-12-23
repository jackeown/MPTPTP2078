%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0373+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 223 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4064,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2476,f2502,f3010,f4028])).

fof(f4028,plain,(
    ~ spl101_2 ),
    inference(avatar_contradiction_clause,[],[f4027])).

fof(f4027,plain,
    ( $false
    | ~ spl101_2 ),
    inference(subsumption_resolution,[],[f3993,f2505])).

fof(f2505,plain,(
    ~ r2_hidden(k1_tarski(sK5),k1_zfmisc_1(sK4)) ),
    inference(subsumption_resolution,[],[f2503,f1098])).

fof(f1098,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f471])).

fof(f471,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f2503,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_zfmisc_1(sK4))
    | v1_xboole_0(k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f1092,f1229])).

fof(f1229,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f867])).

fof(f867,plain,(
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
    inference(nnf_transformation,[],[f547])).

fof(f547,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f455])).

fof(f455,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1092,plain,(
    ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f842])).

fof(f842,plain,
    ( ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(sK4))
    & k1_xboole_0 != sK4
    & m1_subset_1(sK5,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f530,f841])).

fof(f841,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(X1,X0) )
   => ( ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(sK4))
      & k1_xboole_0 != sK4
      & m1_subset_1(sK5,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f530,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f529])).

fof(f529,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      & k1_xboole_0 != X0
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f516])).

fof(f516,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ( k1_xboole_0 != X0
         => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f515])).

fof(f515,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f3993,plain,
    ( r2_hidden(k1_tarski(sK5),k1_zfmisc_1(sK4))
    | ~ spl101_2 ),
    inference(resolution,[],[f2516,f1867])).

fof(f1867,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f1393])).

fof(f1393,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f954])).

fof(f954,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK46(X0,X1),X0)
            | ~ r2_hidden(sK46(X0,X1),X1) )
          & ( r1_tarski(sK46(X0,X1),X0)
            | r2_hidden(sK46(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK46])],[f952,f953])).

fof(f953,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK46(X0,X1),X0)
          | ~ r2_hidden(sK46(X0,X1),X1) )
        & ( r1_tarski(sK46(X0,X1),X0)
          | r2_hidden(sK46(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f952,plain,(
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
    inference(rectify,[],[f951])).

fof(f951,plain,(
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
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f2516,plain,
    ( r1_tarski(k1_tarski(sK5),sK4)
    | ~ spl101_2 ),
    inference(resolution,[],[f2475,f1407])).

fof(f1407,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f963])).

fof(f963,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f2475,plain,
    ( r2_hidden(sK5,sK4)
    | ~ spl101_2 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f2473,plain,
    ( spl101_2
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_2])])).

fof(f3010,plain,
    ( ~ spl101_1
    | spl101_4 ),
    inference(avatar_split_clause,[],[f2599,f2483,f2469])).

fof(f2469,plain,
    ( spl101_1
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f2483,plain,
    ( spl101_4
  <=> sQ100_eqProxy(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_4])])).

fof(f2599,plain,
    ( ~ v1_xboole_0(sK4)
    | spl101_4 ),
    inference(resolution,[],[f2484,f2052])).

fof(f2052,plain,(
    ! [X0] :
      ( sQ100_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f1138,f1996])).

fof(f1996,plain,(
    ! [X1,X0] :
      ( sQ100_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ100_eqProxy])])).

fof(f1138,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f535])).

fof(f535,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2484,plain,
    ( ~ sQ100_eqProxy(k1_xboole_0,sK4)
    | spl101_4 ),
    inference(avatar_component_clause,[],[f2483])).

fof(f2502,plain,(
    ~ spl101_4 ),
    inference(avatar_split_clause,[],[f2032,f2483])).

fof(f2032,plain,(
    ~ sQ100_eqProxy(k1_xboole_0,sK4) ),
    inference(equality_proxy_replacement,[],[f1091,f1996])).

fof(f1091,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f842])).

fof(f2476,plain,
    ( spl101_1
    | spl101_2 ),
    inference(avatar_split_clause,[],[f2465,f2473,f2469])).

fof(f2465,plain,
    ( r2_hidden(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f1090,f1228])).

fof(f1228,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f867])).

fof(f1090,plain,(
    m1_subset_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f842])).
%------------------------------------------------------------------------------
