%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0389+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 242 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f730,f734,f738,f996,f1011,f1023,f1030])).

fof(f1030,plain,
    ( ~ spl12_3
    | ~ spl12_19
    | spl12_22 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_19
    | spl12_22 ),
    inference(subsumption_resolution,[],[f1026,f995])).

fof(f995,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f994])).

fof(f994,plain,
    ( spl12_19
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f1026,plain,
    ( ~ r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | ~ spl12_3
    | spl12_22 ),
    inference(resolution,[],[f1022,f889])).

fof(f889,plain,
    ( ! [X26] :
        ( r2_hidden(X26,sK1)
        | ~ r2_hidden(X26,sK0) )
    | ~ spl12_3 ),
    inference(resolution,[],[f702,f737])).

fof(f737,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl12_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f702,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f626])).

fof(f626,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f624,f625])).

fof(f625,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f623])).

fof(f623,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f593])).

fof(f593,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1022,plain,
    ( ~ r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | spl12_22 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1021,plain,
    ( spl12_22
  <=> r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f1023,plain,
    ( ~ spl12_22
    | spl12_20 ),
    inference(avatar_split_clause,[],[f1018,f1009,f1021])).

fof(f1009,plain,
    ( spl12_20
  <=> r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f1018,plain,
    ( ~ r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK1)
    | spl12_20 ),
    inference(resolution,[],[f1010,f634])).

fof(f634,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f554])).

fof(f554,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f1010,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | spl12_20 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1011,plain,
    ( ~ spl12_20
    | spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f1007,f732,f728,f1009])).

fof(f728,plain,
    ( spl12_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f732,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1007,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f1003,f733])).

fof(f733,plain,
    ( k1_xboole_0 != sK0
    | spl12_2 ),
    inference(avatar_component_clause,[],[f732])).

fof(f1003,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))
    | spl12_1 ),
    inference(resolution,[],[f633,f729])).

fof(f729,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f728])).

fof(f633,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f564,f597])).

fof(f597,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f564,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f563])).

fof(f563,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f558])).

fof(f558,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f996,plain,
    ( spl12_19
    | spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f992,f732,f728,f994])).

fof(f992,plain,
    ( r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f988,f733])).

fof(f988,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)
    | spl12_1 ),
    inference(resolution,[],[f632,f729])).

fof(f632,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f738,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f629,f736])).

fof(f629,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f596])).

fof(f596,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f562,f595])).

fof(f595,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f562,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f561])).

fof(f561,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f560])).

fof(f560,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f559])).

fof(f559,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f734,plain,(
    ~ spl12_2 ),
    inference(avatar_split_clause,[],[f630,f732])).

fof(f630,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f596])).

fof(f730,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f631,f728])).

fof(f631,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f596])).
%------------------------------------------------------------------------------
