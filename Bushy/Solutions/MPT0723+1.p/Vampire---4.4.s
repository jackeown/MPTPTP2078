%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t3_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 7.99s
% Output     : Refutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 654 expanded)
%              Number of leaves         :   60 ( 250 expanded)
%              Depth                    :   15
%              Number of atoms          :  554 (2387 expanded)
%              Number of equality atoms :  102 ( 747 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f81,f88,f95,f105,f119,f126,f133,f149,f156,f163,f173,f180,f187,f206,f213,f220,f227,f234,f256,f263,f270,f287,f325,f332,f346,f353,f360,f367,f374,f387,f394,f440,f447,f454,f470,f477,f484,f509,f516,f530,f1032,f1051,f1079,f1133])).

fof(f1133,plain,
    ( ~ spl7_4
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f1132])).

fof(f1132,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f1094,f87])).

fof(f87,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1094,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl7_88 ),
    inference(superposition,[],[f561,f1078])).

fof(f1078,plain,
    ( sK3 = sK5(k1_enumset1(sK1,sK3,sK2))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f1077,plain,
    ( spl7_88
  <=> sK3 = sK5(k1_enumset1(sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f561,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,sK5(k1_enumset1(X1,X2,X0))) ),
    inference(unit_resulting_resolution,[],[f377,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK5(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK5(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK5(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t7_tarski)).

fof(f377,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f66,f63])).

fof(f63,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f66,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',d1_enumset1)).

fof(f1079,plain,
    ( spl7_88
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1062,f93,f79,f1077])).

fof(f79,plain,
    ( spl7_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f93,plain,
    ( spl7_6
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1062,plain,
    ( sK3 = sK5(k1_enumset1(sK1,sK3,sK2))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f989])).

fof(f989,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | sK5(k1_enumset1(sK1,X2,sK2)) = X2 )
    | ~ spl7_2 ),
    inference(superposition,[],[f552,f970])).

fof(f970,plain,
    ( ! [X12] :
        ( sK1 = sK5(k1_enumset1(sK1,X12,sK2))
        | sK5(k1_enumset1(sK1,X12,sK2)) = X12 )
    | ~ spl7_2 ),
    inference(resolution,[],[f904,f80])).

fof(f80,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f904,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X5)
      | sK5(k1_enumset1(X3,X4,X5)) = X4
      | sK5(k1_enumset1(X3,X4,X5)) = X3 ) ),
    inference(superposition,[],[f545,f660])).

fof(f660,plain,(
    ! [X2,X0,X1] :
      ( sK5(k1_enumset1(X0,X1,X2)) = X2
      | sK5(k1_enumset1(X0,X1,X2)) = X1
      | sK5(k1_enumset1(X0,X1,X2)) = X0 ) ),
    inference(resolution,[],[f544,f430])).

fof(f430,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X0,X3))
      | X1 = X2
      | X0 = X1
      | X1 = X3 ) ),
    inference(resolution,[],[f53,f66])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f544,plain,(
    ! [X2,X0,X1] : r2_hidden(sK5(k1_enumset1(X0,X1,X2)),k1_enumset1(X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f375,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f375,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f545,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,sK5(k1_enumset1(X0,X1,X2))) ),
    inference(unit_resulting_resolution,[],[f375,f67])).

fof(f552,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,sK5(k1_enumset1(X1,X0,X2))) ),
    inference(unit_resulting_resolution,[],[f376,f67])).

fof(f376,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(unit_resulting_resolution,[],[f66,f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X3] :
      ( ~ sP0(X0,X5,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1051,plain,
    ( ~ spl7_87
    | spl7_15
    | spl7_85 ),
    inference(avatar_split_clause,[],[f1044,f1030,f131,f1049])).

fof(f1049,plain,
    ( spl7_87
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f131,plain,
    ( spl7_15
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1030,plain,
    ( spl7_85
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1044,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl7_15
    | ~ spl7_85 ),
    inference(unit_resulting_resolution,[],[f132,f1031,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t2_subset)).

fof(f1031,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f132,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1032,plain,
    ( spl7_82
    | ~ spl7_85
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f988,f79,f1030,f1024])).

fof(f1024,plain,
    ( spl7_82
  <=> ! [X1] : sK5(k1_enumset1(sK1,X1,sK2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f988,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,sK1)
        | sK5(k1_enumset1(sK1,X1,sK2)) = X1 )
    | ~ spl7_2 ),
    inference(superposition,[],[f545,f970])).

fof(f530,plain,
    ( ~ spl7_81
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f409,f344,f528])).

fof(f528,plain,
    ( spl7_81
  <=> ~ r2_hidden(sK4(sK1),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f344,plain,
    ( spl7_50
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f409,plain,
    ( ~ r2_hidden(sK4(sK1),sK5(sK1))
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f345,f67])).

fof(f345,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f344])).

fof(f516,plain,
    ( ~ spl7_79
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f402,f330,f514])).

fof(f514,plain,
    ( spl7_79
  <=> ~ r2_hidden(sK4(sK3),sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f330,plain,
    ( spl7_48
  <=> r2_hidden(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f402,plain,
    ( ~ r2_hidden(sK4(sK3),sK5(sK3))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f331,f67])).

fof(f331,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f330])).

fof(f509,plain,
    ( ~ spl7_77
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f395,f323,f507])).

fof(f507,plain,
    ( spl7_77
  <=> ~ r2_hidden(sK4(sK2),sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f323,plain,
    ( spl7_46
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f395,plain,
    ( ~ r2_hidden(sK4(sK2),sK5(sK2))
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f324,f67])).

fof(f324,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f323])).

fof(f484,plain,
    ( ~ spl7_75
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f302,f218,f482])).

fof(f482,plain,
    ( spl7_75
  <=> ~ r2_hidden(sK5(sK1),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f218,plain,
    ( spl7_32
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f302,plain,
    ( ~ r2_hidden(sK5(sK1),sK5(sK1))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f219,f67])).

fof(f219,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f218])).

fof(f477,plain,
    ( ~ spl7_73
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f295,f211,f475])).

fof(f475,plain,
    ( spl7_73
  <=> ~ r2_hidden(sK5(sK3),sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f211,plain,
    ( spl7_30
  <=> r2_hidden(sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f295,plain,
    ( ~ r2_hidden(sK5(sK3),sK5(sK3))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f212,f67])).

fof(f212,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f211])).

fof(f470,plain,
    ( ~ spl7_71
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f288,f204,f468])).

fof(f468,plain,
    ( spl7_71
  <=> ~ r2_hidden(sK5(sK2),sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f204,plain,
    ( spl7_28
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f288,plain,
    ( ~ r2_hidden(sK5(sK2),sK5(sK2))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f205,f67])).

fof(f205,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f204])).

fof(f454,plain,
    ( ~ spl7_69
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f413,f344,f452])).

fof(f452,plain,
    ( spl7_69
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f413,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl7_50 ),
    inference(unit_resulting_resolution,[],[f345,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',antisymmetry_r2_hidden)).

fof(f447,plain,
    ( ~ spl7_67
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f406,f330,f445])).

fof(f445,plain,
    ( spl7_67
  <=> ~ r2_hidden(sK3,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f406,plain,
    ( ~ r2_hidden(sK3,sK4(sK3))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f331,f47])).

fof(f440,plain,
    ( ~ spl7_65
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f399,f323,f438])).

fof(f438,plain,
    ( spl7_65
  <=> ~ r2_hidden(sK2,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f399,plain,
    ( ~ r2_hidden(sK2,sK4(sK2))
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f324,f47])).

fof(f394,plain,
    ( ~ spl7_63
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f306,f218,f392])).

fof(f392,plain,
    ( spl7_63
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f306,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f219,f47])).

fof(f387,plain,
    ( spl7_60
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f304,f218,f385])).

fof(f385,plain,
    ( spl7_60
  <=> m1_subset_1(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f304,plain,
    ( m1_subset_1(sK5(sK1),sK1)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f219,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t1_subset)).

fof(f374,plain,
    ( ~ spl7_59
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f299,f211,f372])).

fof(f372,plain,
    ( spl7_59
  <=> ~ r2_hidden(sK3,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f299,plain,
    ( ~ r2_hidden(sK3,sK5(sK3))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f212,f47])).

fof(f367,plain,
    ( spl7_56
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f297,f211,f365])).

fof(f365,plain,
    ( spl7_56
  <=> m1_subset_1(sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f297,plain,
    ( m1_subset_1(sK5(sK3),sK3)
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f212,f48])).

fof(f360,plain,
    ( ~ spl7_55
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f292,f204,f358])).

fof(f358,plain,
    ( spl7_55
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f292,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f205,f47])).

fof(f353,plain,
    ( spl7_52
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f290,f204,f351])).

fof(f351,plain,
    ( spl7_52
  <=> m1_subset_1(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f290,plain,
    ( m1_subset_1(sK5(sK2),sK2)
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f205,f48])).

fof(f346,plain,
    ( spl7_50
    | spl7_15 ),
    inference(avatar_split_clause,[],[f243,f131,f344])).

fof(f243,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f132,f45,f46])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',existence_m1_subset_1)).

fof(f332,plain,
    ( spl7_48
    | spl7_13 ),
    inference(avatar_split_clause,[],[f242,f124,f330])).

fof(f124,plain,
    ( spl7_13
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f242,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f125,f45,f46])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f325,plain,
    ( spl7_46
    | spl7_11 ),
    inference(avatar_split_clause,[],[f241,f117,f323])).

fof(f117,plain,
    ( spl7_11
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f241,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f118,f45,f46])).

fof(f118,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f287,plain,
    ( ~ spl7_45
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f198,f93,f285])).

fof(f285,plain,
    ( spl7_45
  <=> ~ r2_hidden(sK3,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f198,plain,
    ( ~ r2_hidden(sK3,sK5(sK1))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f67])).

fof(f270,plain,
    ( ~ spl7_43
    | spl7_15
    | spl7_17 ),
    inference(avatar_split_clause,[],[f237,f147,f131,f268])).

fof(f268,plain,
    ( spl7_43
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f147,plain,
    ( spl7_17
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f148,f132,f46])).

fof(f148,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f263,plain,
    ( ~ spl7_41
    | spl7_13
    | spl7_21 ),
    inference(avatar_split_clause,[],[f236,f161,f124,f261])).

fof(f261,plain,
    ( spl7_41
  <=> ~ m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f161,plain,
    ( spl7_21
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f236,plain,
    ( ~ m1_subset_1(sK1,sK3)
    | ~ spl7_13
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f162,f125,f46])).

fof(f162,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f256,plain,
    ( ~ spl7_39
    | spl7_11
    | spl7_19 ),
    inference(avatar_split_clause,[],[f235,f154,f117,f254])).

fof(f254,plain,
    ( spl7_39
  <=> ~ m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f154,plain,
    ( spl7_19
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f155,f118,f46])).

fof(f155,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f234,plain,
    ( ~ spl7_37
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f197,f86,f232])).

fof(f232,plain,
    ( spl7_37
  <=> ~ r2_hidden(sK2,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f197,plain,
    ( ~ r2_hidden(sK2,sK5(sK3))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f87,f67])).

fof(f227,plain,
    ( ~ spl7_35
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f196,f79,f225])).

fof(f225,plain,
    ( spl7_35
  <=> ~ r2_hidden(sK1,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f196,plain,
    ( ~ r2_hidden(sK1,sK5(sK2))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f80,f67])).

fof(f220,plain,
    ( spl7_32
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f192,f93,f218])).

fof(f192,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f51])).

fof(f213,plain,
    ( spl7_30
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f191,f86,f211])).

fof(f191,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f87,f51])).

fof(f206,plain,
    ( spl7_28
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f190,f79,f204])).

fof(f190,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f80,f51])).

fof(f187,plain,
    ( spl7_26
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f166,f93,f185])).

fof(f185,plain,
    ( spl7_26
  <=> m1_subset_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f166,plain,
    ( m1_subset_1(sK3,sK1)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f48])).

fof(f180,plain,
    ( spl7_24
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f165,f86,f178])).

fof(f178,plain,
    ( spl7_24
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f165,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f87,f48])).

fof(f173,plain,
    ( spl7_22
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f164,f79,f171])).

fof(f171,plain,
    ( spl7_22
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f164,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f80,f48])).

fof(f163,plain,
    ( ~ spl7_21
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f139,f93,f161])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f47])).

fof(f156,plain,
    ( ~ spl7_19
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f138,f86,f154])).

fof(f138,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f87,f47])).

fof(f149,plain,
    ( ~ spl7_17
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f137,f79,f147])).

fof(f137,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f80,f47])).

fof(f133,plain,
    ( ~ spl7_15
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f108,f93,f131])).

fof(f108,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f94,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t7_boole)).

fof(f126,plain,
    ( ~ spl7_13
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f107,f86,f124])).

fof(f107,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f87,f50])).

fof(f119,plain,
    ( ~ spl7_11
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f106,f79,f117])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f80,f50])).

fof(f105,plain,
    ( spl7_8
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f96,f72,f103])).

fof(f103,plain,
    ( spl7_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f72,plain,
    ( spl7_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f96,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_0 ),
    inference(unit_resulting_resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t6_boole)).

fof(f73,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f72])).

fof(f95,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( r2_hidden(sK3,sK1)
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK3,sK1)
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X2,X0)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X2,X0)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',t3_ordinal1)).

fof(f88,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f43,f72])).

fof(f43,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t3_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
