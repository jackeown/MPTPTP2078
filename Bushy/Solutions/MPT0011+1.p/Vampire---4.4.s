%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t4_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 9.46s
% Output     : Refutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 364 expanded)
%              Number of leaves         :   19 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  325 (1803 expanded)
%              Number of equality atoms :   21 (  94 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2013,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f578,f749,f1026,f1027,f1245,f1467,f1468,f1546,f1547,f2012])).

fof(f2012,plain,
    ( spl6_1
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f2006])).

fof(f2006,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_30 ),
    inference(resolution,[],[f1952,f103])).

fof(f103,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_1
  <=> ~ r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1952,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ spl6_30 ),
    inference(resolution,[],[f1943,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d3_tarski)).

fof(f1943,plain,
    ( ! [X14,X15] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(X14,k2_xboole_0(X15,sK2)))
    | ~ spl6_30 ),
    inference(resolution,[],[f1575,f64])).

fof(f64,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f7,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d3_xboole_0)).

fof(f1575,plain,
    ( ! [X2,X3,X1] :
        ( ~ sP0(k2_xboole_0(X2,sK2),X3,X1)
        | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),X1) )
    | ~ spl6_30 ),
    inference(resolution,[],[f1570,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & ~ r2_hidden(sK5(X0,X1,X2),X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & ~ r2_hidden(sK5(X0,X1,X2),X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f1570,plain,
    ( ! [X10] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(X10,sK2))
    | ~ spl6_30 ),
    inference(resolution,[],[f1548,f64])).

fof(f1548,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK2,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),X0) )
    | ~ spl6_30 ),
    inference(resolution,[],[f1126,f56])).

fof(f1126,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1125,plain,
    ( spl6_30
  <=> r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1547,plain,
    ( spl6_28
    | spl6_30
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f1482,f557,f1125,f1119])).

fof(f1119,plain,
    ( spl6_28
  <=> r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f557,plain,
    ( spl6_4
  <=> r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1482,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f558,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f54,f64])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f558,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f557])).

fof(f1546,plain,
    ( spl6_1
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1540])).

fof(f1540,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_28 ),
    inference(resolution,[],[f1529,f103])).

fof(f1529,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ spl6_28 ),
    inference(resolution,[],[f1495,f51])).

fof(f1495,plain,
    ( ! [X11] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK3,X11))
    | ~ spl6_28 ),
    inference(resolution,[],[f1477,f74])).

fof(f74,plain,(
    ! [X2,X3] : sP0(X3,X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f64,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',commutativity_k2_xboole_0)).

fof(f1477,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK3,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),X0) )
    | ~ spl6_28 ),
    inference(resolution,[],[f1120,f56])).

fof(f1120,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK3)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f1468,plain,
    ( spl6_4
    | spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f1133,f102,f563,f557])).

fof(f563,plain,
    ( spl6_6
  <=> r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1133,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK2,sK3))
    | ~ spl6_1 ),
    inference(resolution,[],[f1103,f205])).

fof(f1103,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl6_1 ),
    inference(resolution,[],[f103,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1467,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f1460])).

fof(f1460,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(resolution,[],[f1445,f103])).

fof(f1445,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ spl6_6 ),
    inference(resolution,[],[f1373,f51])).

fof(f1373,plain,
    ( ! [X2,X1] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(X2,k2_xboole_0(sK1,X1)))
    | ~ spl6_6 ),
    inference(superposition,[],[f1349,f44])).

fof(f1349,plain,
    ( ! [X14,X15] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(X14,k2_xboole_0(X15,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f1154,f64])).

fof(f1154,plain,
    ( ! [X2,X3,X1] :
        ( ~ sP0(k2_xboole_0(X2,sK1),X3,X1)
        | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),X1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f1149,f56])).

fof(f1149,plain,
    ( ! [X10] : r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),k2_xboole_0(X10,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f1128,f64])).

fof(f1128,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK1,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f564,f56])).

fof(f564,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f563])).

fof(f1245,plain,
    ( spl6_3
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1240])).

fof(f1240,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f1228,f109])).

fof(f109,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_3
  <=> ~ r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1228,plain,
    ( r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl6_14 ),
    inference(resolution,[],[f1212,f51])).

fof(f1212,plain,
    ( ! [X11] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,X11))
    | ~ spl6_14 ),
    inference(resolution,[],[f1104,f74])).

fof(f1104,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK1,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f598,f56])).

fof(f598,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl6_14
  <=> r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1027,plain,
    ( spl6_12
    | spl6_14
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f758,f570,f597,f591])).

fof(f591,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f570,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f758,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK1)
    | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f571,f205])).

fof(f571,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f570])).

fof(f1026,plain,
    ( spl6_3
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_12 ),
    inference(resolution,[],[f1006,f109])).

fof(f1006,plain,
    ( r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl6_12 ),
    inference(resolution,[],[f931,f51])).

fof(f931,plain,
    ( ! [X2,X1] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X2,k2_xboole_0(sK2,X1)))
    | ~ spl6_12 ),
    inference(superposition,[],[f916,f44])).

fof(f916,plain,
    ( ! [X14,X15] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X14,k2_xboole_0(X15,sK2)))
    | ~ spl6_12 ),
    inference(resolution,[],[f773,f64])).

fof(f773,plain,
    ( ! [X2,X3,X1] :
        ( ~ sP0(k2_xboole_0(X2,sK2),X3,X1)
        | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X1) )
    | ~ spl6_12 ),
    inference(resolution,[],[f766,f56])).

fof(f766,plain,
    ( ! [X0] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK2))
    | ~ spl6_12 ),
    inference(resolution,[],[f750,f64])).

fof(f750,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK2,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f592,f56])).

fof(f592,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f591])).

fof(f749,plain,
    ( spl6_3
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(resolution,[],[f697,f109])).

fof(f697,plain,
    ( r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | ~ spl6_10 ),
    inference(resolution,[],[f686,f51])).

fof(f686,plain,
    ( ! [X0,X1] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,k2_xboole_0(X1,sK3)))
    | ~ spl6_10 ),
    inference(resolution,[],[f618,f64])).

fof(f618,plain,
    ( ! [X2,X3,X1] :
        ( ~ sP0(k2_xboole_0(X2,sK3),X3,X1)
        | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f612,f56])).

fof(f612,plain,
    ( ! [X0] : r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(X0,sK3))
    | ~ spl6_10 ),
    inference(resolution,[],[f600,f64])).

fof(f600,plain,
    ( ! [X0,X1] :
        ( ~ sP0(sK3,X1,X0)
        | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),X0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f577,f56])).

fof(f577,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl6_10
  <=> r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f578,plain,
    ( spl6_8
    | spl6_10
    | spl6_3 ),
    inference(avatar_split_clause,[],[f524,f108,f576,f570])).

fof(f524,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),sK3)
    | r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK1,sK2))
    | ~ spl6_3 ),
    inference(resolution,[],[f205,f117])).

fof(f117,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f109,f50])).

fof(f115,plain,
    ( ~ spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f93,f102,f108])).

fof(f93,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(extensionality_resolution,[],[f48,f75])).

fof(f75,plain,(
    k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != k2_xboole_0(sK3,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f39,f44])).

fof(f39,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2)
   => k2_xboole_0(k2_xboole_0(sK1,sK2),sK3) != k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',t4_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t4_xboole_1.p',d10_xboole_0)).
%------------------------------------------------------------------------------
