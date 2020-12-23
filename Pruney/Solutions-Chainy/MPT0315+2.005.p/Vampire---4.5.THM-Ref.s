%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 148 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :    6
%              Number of atoms          :  242 ( 400 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f43,f47,f51,f55,f59,f67,f71,f75,f85,f99,f108,f113,f140,f143,f149,f474,f530])).

fof(f530,plain,
    ( spl7_1
    | ~ spl7_64 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl7_1
    | ~ spl7_64 ),
    inference(resolution,[],[f473,f33])).

fof(f33,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl7_1
  <=> r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f473,plain,
    ( ! [X4,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl7_64
  <=> ! [X3,X4] : r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f474,plain,
    ( spl7_64
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f470,f146,f111,f83,f472])).

fof(f83,plain,
    ( spl7_13
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f111,plain,
    ( spl7_17
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f146,plain,
    ( spl7_23
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f470,plain,
    ( ! [X4,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))
    | ~ spl7_13
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f442,f84])).

fof(f84,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f442,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(sK4(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4)),sK0,X3,sK1,X4),k1_xboole_0)
        | r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4)) )
    | ~ spl7_17
    | ~ spl7_23 ),
    inference(superposition,[],[f112,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f146])).

fof(f112,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f149,plain,
    ( spl7_23
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f144,f65,f36,f146])).

fof(f36,plain,
    ( spl7_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f65,plain,
    ( spl7_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f144,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl7_2
    | ~ spl7_9 ),
    inference(resolution,[],[f38,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f38,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f143,plain,
    ( spl7_1
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl7_1
    | ~ spl7_22 ),
    inference(resolution,[],[f139,f33])).

fof(f139,plain,
    ( ! [X4,X3] : r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_22
  <=> ! [X3,X4] : r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f140,plain,
    ( spl7_22
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f136,f106,f96,f83,f138])).

fof(f96,plain,
    ( spl7_15
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f106,plain,
    ( spl7_16
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f136,plain,
    ( ! [X4,X3] : r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f118,f84])).

fof(f118,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK6(sK4(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3)),X3,sK2,X4,sK3),k1_xboole_0)
        | r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3)) )
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(superposition,[],[f107,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f107,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( spl7_17
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f109,f73,f57,f111])).

fof(f57,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f73,plain,
    ( spl7_11
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f109,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f74,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
        | r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f108,plain,
    ( spl7_16
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f104,f69,f57,f106])).

fof(f69,plain,
    ( spl7_10
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f104,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3))
        | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(resolution,[],[f70,f58])).

fof(f70,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))
        | r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f99,plain,
    ( spl7_15
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f92,f65,f40,f96])).

fof(f40,plain,
    ( spl7_3
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f92,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f85,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f81,f53,f49,f45,f83])).

fof(f45,plain,
    ( spl7_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f49,plain,
    ( spl7_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f53,plain,
    ( spl7_6
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f81,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f80,f46])).

fof(f46,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f75,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f28,f73])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f11,f17])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))
        & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,k3_xboole_0(X2,X4))
          & r2_hidden(X5,k3_xboole_0(X1,X3))
          & k4_tarski(X5,X6) = X0 )
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f71,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))
      | ~ r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f55,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f43,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f19,f40,f36])).

fof(f19,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
    & ( r1_xboole_0(sK2,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))
      & ( r1_xboole_0(sK2,sK3)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f34,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (2079)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (2077)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (2075)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (2076)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (2078)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (2075)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f531,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f34,f43,f47,f51,f55,f59,f67,f71,f75,f85,f99,f108,f113,f140,f143,f149,f474,f530])).
% 0.21/0.43  fof(f530,plain,(
% 0.21/0.43    spl7_1 | ~spl7_64),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f525])).
% 0.21/0.43  fof(f525,plain,(
% 0.21/0.43    $false | (spl7_1 | ~spl7_64)),
% 0.21/0.43    inference(resolution,[],[f473,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) | spl7_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl7_1 <=> r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.43  fof(f473,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))) ) | ~spl7_64),
% 0.21/0.43    inference(avatar_component_clause,[],[f472])).
% 0.21/0.43  fof(f472,plain,(
% 0.21/0.43    spl7_64 <=> ! [X3,X4] : r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.21/0.43  fof(f474,plain,(
% 0.21/0.43    spl7_64 | ~spl7_13 | ~spl7_17 | ~spl7_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f470,f146,f111,f83,f472])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl7_13 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    spl7_17 <=> ! [X1,X3,X0,X2] : (r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    spl7_23 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.43  fof(f470,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))) ) | (~spl7_13 | ~spl7_17 | ~spl7_23)),
% 0.21/0.43    inference(subsumption_resolution,[],[f442,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl7_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f83])).
% 0.21/0.43  fof(f442,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r2_hidden(sK5(sK4(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4)),sK0,X3,sK1,X4),k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK1,X4))) ) | (~spl7_17 | ~spl7_23)),
% 0.21/0.43    inference(superposition,[],[f112,f148])).
% 0.21/0.43  fof(f148,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl7_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f146])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl7_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f111])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    spl7_23 | ~spl7_2 | ~spl7_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f144,f65,f36,f146])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl7_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl7_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl7_2 | ~spl7_9)),
% 0.21/0.43    inference(resolution,[],[f38,f66])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl7_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK1) | ~spl7_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f36])).
% 0.21/0.43  fof(f143,plain,(
% 0.21/0.43    spl7_1 | ~spl7_22),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    $false | (spl7_1 | ~spl7_22)),
% 0.21/0.43    inference(resolution,[],[f139,f33])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))) ) | ~spl7_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f138])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    spl7_22 <=> ! [X3,X4] : r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    spl7_22 | ~spl7_13 | ~spl7_15 | ~spl7_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f136,f106,f96,f83,f138])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl7_15 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    spl7_16 <=> ! [X1,X3,X0,X2] : (r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))) ) | (~spl7_13 | ~spl7_15 | ~spl7_16)),
% 0.21/0.43    inference(subsumption_resolution,[],[f118,f84])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r2_hidden(sK6(sK4(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3)),X3,sK2,X4,sK3),k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X4,sK3))) ) | (~spl7_15 | ~spl7_16)),
% 0.21/0.43    inference(superposition,[],[f107,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl7_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f96])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | ~spl7_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f106])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl7_17 | ~spl7_7 | ~spl7_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f109,f73,f57,f111])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl7_7 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl7_11 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X0,X2)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | (~spl7_7 | ~spl7_11)),
% 0.21/0.43    inference(resolution,[],[f74,f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl7_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3))) ) | ~spl7_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    spl7_16 | ~spl7_7 | ~spl7_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f104,f69,f57,f106])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl7_10 <=> ! [X1,X3,X0,X2,X4] : (r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(sK4(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)),X0,X1,X2,X3),k3_xboole_0(X1,X3)) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) ) | (~spl7_7 | ~spl7_10)),
% 0.21/0.43    inference(resolution,[],[f70,f58])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) | r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4))) ) | ~spl7_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f69])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl7_15 | ~spl7_3 | ~spl7_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f92,f65,f40,f96])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl7_3 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK2,sK3) | (~spl7_3 | ~spl7_9)),
% 0.21/0.43    inference(resolution,[],[f66,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK3) | ~spl7_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl7_13 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f81,f53,f49,f45,f83])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl7_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl7_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl7_6 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.21/0.43    inference(subsumption_resolution,[],[f80,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl7_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | (~spl7_5 | ~spl7_6)),
% 0.21/0.43    inference(superposition,[],[f54,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl7_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl7_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl7_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f73])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4] : ((r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f11,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X4,X3,X2,X1,X0] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) => (r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) & r2_hidden(sK5(X0,X1,X2,X3,X4),k3_xboole_0(X1,X3)) & k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)) = X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4] : (? [X5,X6] : (r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl7_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f69])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X2,X3,X4),k3_xboole_0(X2,X4)) | ~r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl7_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f65])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl7_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl7_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl7_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl7_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl7_2 | spl7_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f40,f36])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1))) => (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) & (r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~spl7_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f31])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (2075)------------------------------
% 0.21/0.43  % (2075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (2075)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (2075)Memory used [KB]: 11001
% 0.21/0.43  % (2075)Time elapsed: 0.012 s
% 0.21/0.43  % (2075)------------------------------
% 0.21/0.43  % (2075)------------------------------
% 0.21/0.43  % (2069)Success in time 0.069 s
%------------------------------------------------------------------------------
