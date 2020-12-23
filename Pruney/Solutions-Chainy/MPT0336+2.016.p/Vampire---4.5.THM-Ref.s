%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 189 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  288 ( 482 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1635,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f90,f95,f1018,f1026,f1030,f1052,f1433,f1440,f1497,f1502,f1506,f1560,f1634])).

fof(f1634,plain,
    ( spl6_1
    | ~ spl6_111 ),
    inference(avatar_split_clause,[],[f1628,f1557,f64])).

fof(f64,plain,
    ( spl6_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1557,plain,
    ( spl6_111
  <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f1628,plain,
    ( r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl6_111 ),
    inference(resolution,[],[f1559,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1559,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f1560,plain,
    ( spl6_111
    | ~ spl6_6
    | ~ spl6_69 ),
    inference(avatar_split_clause,[],[f1555,f772,f92,f1557])).

fof(f92,plain,
    ( spl6_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f772,plain,
    ( spl6_69
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f1555,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl6_6
    | ~ spl6_69 ),
    inference(forward_demodulation,[],[f1554,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1554,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_69 ),
    inference(trivial_inequality_removal,[],[f1543])).

fof(f1543,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_69 ),
    inference(superposition,[],[f301,f774])).

fof(f774,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f772])).

fof(f301,plain,
    ( ! [X7] :
        ( k1_xboole_0 != k3_xboole_0(sK1,X7)
        | r1_xboole_0(sK1,k2_xboole_0(sK2,X7)) )
    | ~ spl6_6 ),
    inference(superposition,[],[f59,f97])).

fof(f97,plain,
    ( ! [X0] : k3_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK1,X0)
    | ~ spl6_6 ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f94,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1506,plain,
    ( spl6_69
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f1504,f764,f772])).

fof(f764,plain,
    ( spl6_68
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1504,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl6_68 ),
    inference(resolution,[],[f766,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f766,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f764])).

fof(f1502,plain,
    ( spl6_68
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f1500,f751,f764])).

fof(f751,plain,
    ( spl6_66
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f1500,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_66 ),
    inference(resolution,[],[f753,f57])).

fof(f753,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f751])).

fof(f1497,plain,
    ( spl6_66
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f747,f397,f751])).

fof(f397,plain,
    ( spl6_31
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f747,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_31 ),
    inference(resolution,[],[f398,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f398,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f397])).

fof(f1440,plain,
    ( ~ spl6_64
    | spl6_31
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f1058,f370,f397,f737])).

fof(f737,plain,
    ( spl6_64
  <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f370,plain,
    ( spl6_26
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1058,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
        | ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) )
    | ~ spl6_26 ),
    inference(superposition,[],[f51,f372])).

fof(f372,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f370])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1433,plain,
    ( ~ spl6_5
    | spl6_79 ),
    inference(avatar_contradiction_clause,[],[f1421])).

fof(f1421,plain,
    ( $false
    | ~ spl6_5
    | spl6_79 ),
    inference(resolution,[],[f1404,f1025])).

fof(f1025,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl6_79 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f1023,plain,
    ( spl6_79
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1404,plain,
    ( ! [X2] : r1_xboole_0(k3_xboole_0(X2,sK1),sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f1383,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1383,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK1,X0),sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f304,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f304,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0)
        | r1_xboole_0(k3_xboole_0(sK1,X0),sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f114,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_xboole_0(X1,k1_xboole_0)
        | r1_xboole_0(X1,sK2) )
    | ~ spl6_5 ),
    inference(superposition,[],[f62,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_5
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1052,plain,
    ( spl6_26
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f1043,f217,f370])).

fof(f217,plain,
    ( spl6_18
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1043,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | ~ spl6_18 ),
    inference(superposition,[],[f46,f219])).

fof(f219,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1030,plain,
    ( spl6_18
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f1029,f79,f217])).

fof(f79,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1029,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f81,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1026,plain,
    ( ~ spl6_79
    | ~ spl6_3
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f1019,f855,f74,f1023])).

fof(f74,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f855,plain,
    ( spl6_73
  <=> r2_hidden(sK3,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f1019,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl6_3
    | ~ spl6_73 ),
    inference(resolution,[],[f857,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f76,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f857,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f855])).

fof(f1018,plain,
    ( spl6_73
    | spl6_64 ),
    inference(avatar_split_clause,[],[f853,f737,f855])).

fof(f853,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | spl6_64 ),
    inference(resolution,[],[f738,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f738,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | spl6_64 ),
    inference(avatar_component_clause,[],[f737])).

fof(f95,plain,
    ( spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f85,f69,f92])).

fof(f69,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f85,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f90,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f84,f69,f87])).

fof(f84,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f71,f58])).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f31])).

fof(f31,plain,
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

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f77,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f41,f64])).

fof(f41,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (14563)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (14563)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f1635,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f90,f95,f1018,f1026,f1030,f1052,f1433,f1440,f1497,f1502,f1506,f1560,f1634])).
% 0.21/0.44  fof(f1634,plain,(
% 0.21/0.44    spl6_1 | ~spl6_111),
% 0.21/0.44    inference(avatar_split_clause,[],[f1628,f1557,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl6_1 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.44  fof(f1557,plain,(
% 0.21/0.44    spl6_111 <=> r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 0.21/0.44  fof(f1628,plain,(
% 0.21/0.44    r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl6_111),
% 0.21/0.44    inference(resolution,[],[f1559,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.44  fof(f1559,plain,(
% 0.21/0.44    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl6_111),
% 0.21/0.44    inference(avatar_component_clause,[],[f1557])).
% 0.21/0.44  fof(f1560,plain,(
% 0.21/0.44    spl6_111 | ~spl6_6 | ~spl6_69),
% 0.21/0.44    inference(avatar_split_clause,[],[f1555,f772,f92,f1557])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl6_6 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.44  fof(f772,plain,(
% 0.21/0.44    spl6_69 <=> k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 0.21/0.44  fof(f1555,plain,(
% 0.21/0.44    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | (~spl6_6 | ~spl6_69)),
% 0.21/0.44    inference(forward_demodulation,[],[f1554,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.44  fof(f1554,plain,(
% 0.21/0.44    r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | (~spl6_6 | ~spl6_69)),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f1543])).
% 0.21/0.44  fof(f1543,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) | (~spl6_6 | ~spl6_69)),
% 0.21/0.44    inference(superposition,[],[f301,f774])).
% 0.21/0.44  fof(f774,plain,(
% 0.21/0.44    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl6_69),
% 0.21/0.44    inference(avatar_component_clause,[],[f772])).
% 0.21/0.44  fof(f301,plain,(
% 0.21/0.44    ( ! [X7] : (k1_xboole_0 != k3_xboole_0(sK1,X7) | r1_xboole_0(sK1,k2_xboole_0(sK2,X7))) ) | ~spl6_6),
% 0.21/0.44    inference(superposition,[],[f59,f97])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ( ! [X0] : (k3_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK1,X0)) ) | ~spl6_6),
% 0.21/0.44    inference(resolution,[],[f94,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK2) | ~spl6_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.44  fof(f1506,plain,(
% 0.21/0.44    spl6_69 | ~spl6_68),
% 0.21/0.44    inference(avatar_split_clause,[],[f1504,f764,f772])).
% 0.21/0.44  fof(f764,plain,(
% 0.21/0.44    spl6_68 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.21/0.44  fof(f1504,plain,(
% 0.21/0.44    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl6_68),
% 0.21/0.44    inference(resolution,[],[f766,f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f37])).
% 0.21/0.44  fof(f766,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK0) | ~spl6_68),
% 0.21/0.44    inference(avatar_component_clause,[],[f764])).
% 0.21/0.44  fof(f1502,plain,(
% 0.21/0.44    spl6_68 | ~spl6_66),
% 0.21/0.44    inference(avatar_split_clause,[],[f1500,f751,f764])).
% 0.21/0.44  fof(f751,plain,(
% 0.21/0.44    spl6_66 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.21/0.44  fof(f1500,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK0) | ~spl6_66),
% 0.21/0.44    inference(resolution,[],[f753,f57])).
% 0.21/0.44  fof(f753,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~spl6_66),
% 0.21/0.44    inference(avatar_component_clause,[],[f751])).
% 0.21/0.44  fof(f1497,plain,(
% 0.21/0.44    spl6_66 | ~spl6_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f747,f397,f751])).
% 0.21/0.44  fof(f397,plain,(
% 0.21/0.44    spl6_31 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.44  fof(f747,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1) | ~spl6_31),
% 0.21/0.44    inference(resolution,[],[f398,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.44  fof(f398,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl6_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f397])).
% 0.21/0.44  fof(f1440,plain,(
% 0.21/0.44    ~spl6_64 | spl6_31 | ~spl6_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f1058,f370,f397,f737])).
% 0.21/0.44  fof(f737,plain,(
% 0.21/0.44    spl6_64 <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.21/0.44  fof(f370,plain,(
% 0.21/0.44    spl6_26 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.44  fof(f1058,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))) ) | ~spl6_26),
% 0.21/0.44    inference(superposition,[],[f51,f372])).
% 0.21/0.44  fof(f372,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | ~spl6_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f370])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f34])).
% 0.21/0.44  fof(f1433,plain,(
% 0.21/0.44    ~spl6_5 | spl6_79),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f1421])).
% 0.21/0.44  fof(f1421,plain,(
% 0.21/0.44    $false | (~spl6_5 | spl6_79)),
% 0.21/0.44    inference(resolution,[],[f1404,f1025])).
% 0.21/0.44  fof(f1025,plain,(
% 0.21/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl6_79),
% 0.21/0.44    inference(avatar_component_clause,[],[f1023])).
% 0.21/0.44  fof(f1023,plain,(
% 0.21/0.44    spl6_79 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 0.21/0.44  fof(f1404,plain,(
% 0.21/0.44    ( ! [X2] : (r1_xboole_0(k3_xboole_0(X2,sK1),sK2)) ) | ~spl6_5),
% 0.21/0.44    inference(superposition,[],[f1383,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.44  fof(f1383,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK1,X0),sK2)) ) | ~spl6_5),
% 0.21/0.44    inference(resolution,[],[f304,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.44  fof(f304,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) | r1_xboole_0(k3_xboole_0(sK1,X0),sK2)) ) | ~spl6_5),
% 0.21/0.44    inference(resolution,[],[f114,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    ( ! [X1] : (~r1_tarski(X1,sK1) | ~r1_xboole_0(X1,k1_xboole_0) | r1_xboole_0(X1,sK2)) ) | ~spl6_5),
% 0.21/0.44    inference(superposition,[],[f62,f89])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl6_5 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.44  fof(f1052,plain,(
% 0.21/0.44    spl6_26 | ~spl6_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f1043,f217,f370])).
% 0.21/0.44  fof(f217,plain,(
% 0.21/0.44    spl6_18 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.44  fof(f1043,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | ~spl6_18),
% 0.21/0.44    inference(superposition,[],[f46,f219])).
% 0.21/0.44  fof(f219,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f217])).
% 0.21/0.44  fof(f1030,plain,(
% 0.21/0.44    spl6_18 | ~spl6_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f1029,f79,f217])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.44  fof(f1029,plain,(
% 0.21/0.44    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 0.21/0.44    inference(resolution,[],[f81,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f79])).
% 0.21/0.44  fof(f1026,plain,(
% 0.21/0.44    ~spl6_79 | ~spl6_3 | ~spl6_73),
% 0.21/0.44    inference(avatar_split_clause,[],[f1019,f855,f74,f1023])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl6_3 <=> r2_hidden(sK3,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.44  fof(f855,plain,(
% 0.21/0.44    spl6_73 <=> r2_hidden(sK3,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 0.21/0.44  fof(f1019,plain,(
% 0.21/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | (~spl6_3 | ~spl6_73)),
% 0.21/0.44    inference(resolution,[],[f857,f96])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) ) | ~spl6_3),
% 0.21/0.44    inference(resolution,[],[f76,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    r2_hidden(sK3,sK2) | ~spl6_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f74])).
% 0.21/0.44  fof(f857,plain,(
% 0.21/0.44    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | ~spl6_73),
% 0.21/0.44    inference(avatar_component_clause,[],[f855])).
% 0.21/0.44  fof(f1018,plain,(
% 0.21/0.44    spl6_73 | spl6_64),
% 0.21/0.44    inference(avatar_split_clause,[],[f853,f737,f855])).
% 0.21/0.44  fof(f853,plain,(
% 0.21/0.44    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | spl6_64),
% 0.21/0.44    inference(resolution,[],[f738,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,axiom,(
% 0.21/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.44  fof(f738,plain,(
% 0.21/0.44    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | spl6_64),
% 0.21/0.44    inference(avatar_component_clause,[],[f737])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl6_6 | ~spl6_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f85,f69,f92])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    r1_xboole_0(sK1,sK2) | ~spl6_2),
% 0.21/0.44    inference(resolution,[],[f71,f57])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f69])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl6_5 | ~spl6_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f84,f69,f87])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl6_2),
% 0.21/0.44    inference(resolution,[],[f71,f58])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl6_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f79])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.44    inference(ennf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f18])).
% 0.21/0.44  fof(f18,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl6_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f74])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    r2_hidden(sK3,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl6_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f40,f69])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    r1_xboole_0(sK2,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ~spl6_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f41,f64])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14563)------------------------------
% 0.21/0.44  % (14563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14563)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14563)Memory used [KB]: 11513
% 0.21/0.44  % (14563)Time elapsed: 0.031 s
% 0.21/0.44  % (14563)------------------------------
% 0.21/0.44  % (14563)------------------------------
% 0.21/0.44  % (14551)Success in time 0.085 s
%------------------------------------------------------------------------------
