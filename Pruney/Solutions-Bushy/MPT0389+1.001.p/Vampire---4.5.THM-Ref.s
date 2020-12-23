%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:53 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 193 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  359 ( 731 expanded)
%              Number of equality atoms :   63 ( 158 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f91,f106,f118,f308,f539,f813,f832,f1156,f1345,f1346,f1541,f1543,f2835])).

fof(f2835,plain,
    ( ~ spl7_79
    | spl7_18
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f2815,f271,f226,f1053])).

fof(f1053,plain,
    ( spl7_79
  <=> r2_hidden(sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f226,plain,
    ( spl7_18
  <=> r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f271,plain,
    ( spl7_23
  <=> ! [X0] :
        ( r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),X0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f2815,plain,
    ( ~ r2_hidden(sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0))),sK1)
    | spl7_18
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f228,f272])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),X0) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f271])).

fof(f228,plain,
    ( ~ r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0))))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1543,plain,
    ( spl7_79
    | spl7_2
    | ~ spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f1525,f141,f82,f77,f1053])).

fof(f77,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f82,plain,
    ( spl7_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f141,plain,
    ( spl7_11
  <=> r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1525,plain,
    ( r2_hidden(sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0))),sK1)
    | spl7_2
    | ~ spl7_3
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f143,f164])).

fof(f164,plain,
    ( ! [X10] :
        ( r2_hidden(sK5(sK0,X10),sK1)
        | r2_hidden(X10,k1_setfam_1(sK0)) )
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f161,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK0
    | spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f161,plain,
    ( ! [X10] :
        ( r2_hidden(sK5(sK0,X10),sK1)
        | r2_hidden(X10,k1_setfam_1(sK0))
        | k1_xboole_0 = sK0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f101,f69])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | r2_hidden(sK5(X0,X5),X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(sK5(X0,X5),X0)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),X0) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK3(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK5(X0,X5))
                    & r2_hidden(sK5(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK3(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK3(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK3(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK5(X0,X5))
        & r2_hidden(sK5(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f143,plain,
    ( ~ r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1541,plain,
    ( ~ spl7_18
    | spl7_2
    | spl7_11 ),
    inference(avatar_split_clause,[],[f1527,f141,f77,f226])).

fof(f1527,plain,
    ( ~ r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),sK5(sK0,sK6(k1_setfam_1(sK1),k1_setfam_1(sK0))))
    | spl7_2
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f79,f143,f68])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,k1_setfam_1(X0))
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X5,sK5(X0,X5))
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1346,plain,
    ( spl7_12
    | spl7_1 ),
    inference(avatar_split_clause,[],[f1334,f72,f146])).

fof(f146,plain,
    ( spl7_12
  <=> r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f72,plain,
    ( spl7_1
  <=> r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1334,plain,
    ( r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f1345,plain,
    ( ~ spl7_11
    | spl7_1 ),
    inference(avatar_split_clause,[],[f1335,f72,f141])).

fof(f1335,plain,
    ( ~ r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1156,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f832,plain,
    ( spl7_44
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f826,f608,f549])).

fof(f549,plain,
    ( spl7_44
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f608,plain,
    ( spl7_47
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f826,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_47 ),
    inference(backward_demodulation,[],[f43,f610])).

fof(f610,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f608])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f813,plain,(
    spl7_47 ),
    inference(avatar_contradiction_clause,[],[f812])).

fof(f812,plain,
    ( $false
    | spl7_47 ),
    inference(subsumption_resolution,[],[f807,f43])).

fof(f807,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl7_47 ),
    inference(unit_resulting_resolution,[],[f609,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f609,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | spl7_47 ),
    inference(avatar_component_clause,[],[f608])).

fof(f539,plain,
    ( spl7_16
    | spl7_23
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f520,f146,f271,f200])).

fof(f200,plain,
    ( spl7_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f520,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),X0)
        | ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = sK1 )
    | ~ spl7_12 ),
    inference(resolution,[],[f148,f70])).

fof(f70,plain,(
    ! [X0,X7,X5] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X7,X5,X1] :
      ( r2_hidden(X5,X7)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(X5,X1)
      | k1_setfam_1(X0) != X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f148,plain,
    ( r2_hidden(sK6(k1_setfam_1(sK1),k1_setfam_1(sK0)),k1_setfam_1(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f308,plain,
    ( spl7_4
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f288,f90])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f288,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f45,f113,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f113,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f118,plain,
    ( spl7_7
    | ~ spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f108,f103,f115,f112])).

fof(f115,plain,
    ( spl7_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f103,plain,
    ( spl7_6
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f105,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f105,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f99,f82,f103])).

fof(f99,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK1))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,
    ( ~ spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f86,f77,f88])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f79,f44])).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f80,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
