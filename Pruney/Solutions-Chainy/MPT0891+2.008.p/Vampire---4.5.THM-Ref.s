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
% DateTime   : Thu Dec  3 12:59:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 289 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  438 (1088 expanded)
%              Number of equality atoms :  235 ( 632 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f282,f301,f392,f416,f433,f528])).

fof(f528,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f152,f90,f177,f450])).

fof(f450,plain,
    ( ! [X0] :
        ( sK3 != sK4(X0)
        | ~ r2_hidden(sK3,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_13 ),
    inference(superposition,[],[f58,f281])).

fof(f281,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl7_13
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f58,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f177,plain,(
    ! [X1] : sK4(k1_tarski(X1)) = X1 ),
    inference(subsumption_resolution,[],[f126,f152])).

fof(f126,plain,(
    ! [X1] :
      ( sK4(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f90,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f141,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f141,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X0,X1) ),
    inference(subsumption_resolution,[],[f139,f134])).

fof(f134,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f64,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_tarski(X0,X1)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f433,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f432,f121,f116,f111,f106,f97,f211])).

fof(f211,plain,
    ( spl7_9
  <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f97,plain,
    ( spl7_2
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f106,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f111,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f116,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f121,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f432,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f431,f123])).

fof(f123,plain,
    ( k1_xboole_0 != sK0
    | spl7_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f431,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f430,f118])).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | spl7_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f430,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f429,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK2
    | spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f429,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f427,f108])).

fof(f108,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f427,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(superposition,[],[f49,f99])).

fof(f99,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f416,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f414,f123])).

fof(f414,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f413,f118])).

fof(f413,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f412,f113])).

fof(f412,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f411,f108])).

fof(f411,plain,
    ( ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f403,f149])).

fof(f149,plain,(
    ! [X4,X5,X3] : k3_mcart_1(X3,X4,X5) != X5 ),
    inference(superposition,[],[f130,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f130,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f80,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f80,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f403,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_3 ),
    inference(superposition,[],[f49,f103])).

fof(f103,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl7_3
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

% (26343)Refutation not found, incomplete strategy% (26343)------------------------------
% (26343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f392,plain,(
    ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f152,f90,f177,f341])).

fof(f341,plain,
    ( ! [X1] :
        ( sK3 != sK4(X1)
        | ~ r2_hidden(sK3,X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_11 ),
    inference(superposition,[],[f57,f234])).

fof(f234,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_11
  <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f57,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f301,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f300,f121,f116,f111,f106,f93,f232])).

fof(f93,plain,
    ( spl7_1
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f300,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f299,f123])).

fof(f299,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f298,f118])).

fof(f298,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4
    | spl7_5 ),
    inference(subsumption_resolution,[],[f297,f113])).

fof(f297,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f290,f108])).

fof(f290,plain,
    ( sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_1 ),
    inference(superposition,[],[f49,f95])).

fof(f95,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f282,plain,
    ( spl7_13
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f277,f211,f121,f116,f111,f106,f279])).

fof(f277,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | spl7_7
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f276,f123])).

fof(f276,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | spl7_5
    | spl7_6
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f275,f118])).

fof(f275,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f274,f113])).

fof(f274,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f259,f108])).

fof(f259,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))
    | ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(superposition,[],[f213,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f213,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f211])).

fof(f124,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f41,f121])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
      | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
          | k6_mcart_1(sK0,sK1,sK2,X3) = X3
          | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
        | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) )
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f119,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f43,f111])).

fof(f43,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f44,f106])).

fof(f44,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,
    ( spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f45,f101,f97,f93])).

fof(f45,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:08:51 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.50  % (26320)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (26336)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (26327)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (26335)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (26318)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (26338)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (26315)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (26330)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (26321)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26319)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (26328)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (26326)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (26316)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (26322)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (26317)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (26343)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (26334)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26339)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (26327)Refutation not found, incomplete strategy% (26327)------------------------------
% 0.21/0.53  % (26327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26327)Memory used [KB]: 10746
% 0.21/0.53  % (26327)Time elapsed: 0.108 s
% 0.21/0.53  % (26327)------------------------------
% 0.21/0.53  % (26327)------------------------------
% 0.21/0.54  % (26336)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (26331)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (26342)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (26337)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (26324)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (26342)Refutation not found, incomplete strategy% (26342)------------------------------
% 0.21/0.54  % (26342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26344)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (26329)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (26344)Refutation not found, incomplete strategy% (26344)------------------------------
% 0.21/0.54  % (26344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26344)Memory used [KB]: 1663
% 0.21/0.54  % (26344)Time elapsed: 0.002 s
% 0.21/0.54  % (26344)------------------------------
% 0.21/0.54  % (26344)------------------------------
% 0.21/0.54  % (26329)Refutation not found, incomplete strategy% (26329)------------------------------
% 0.21/0.54  % (26329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26329)Memory used [KB]: 1791
% 0.21/0.54  % (26329)Time elapsed: 0.139 s
% 0.21/0.54  % (26329)------------------------------
% 0.21/0.54  % (26329)------------------------------
% 0.21/0.54  % (26340)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (26325)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (26333)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (26332)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (26333)Refutation not found, incomplete strategy% (26333)------------------------------
% 0.21/0.55  % (26333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26333)Memory used [KB]: 1791
% 0.21/0.55  % (26333)Time elapsed: 0.138 s
% 0.21/0.55  % (26333)------------------------------
% 0.21/0.55  % (26333)------------------------------
% 0.21/0.55  % (26323)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (26332)Refutation not found, incomplete strategy% (26332)------------------------------
% 0.21/0.55  % (26332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26332)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26332)Memory used [KB]: 1791
% 0.21/0.55  % (26332)Time elapsed: 0.139 s
% 0.21/0.55  % (26332)------------------------------
% 0.21/0.55  % (26332)------------------------------
% 0.21/0.55  % (26341)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (26342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26342)Memory used [KB]: 6268
% 0.21/0.55  % (26342)Time elapsed: 0.129 s
% 0.21/0.55  % (26342)------------------------------
% 0.21/0.55  % (26342)------------------------------
% 0.21/0.55  % (26341)Refutation not found, incomplete strategy% (26341)------------------------------
% 0.21/0.55  % (26341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26331)Refutation not found, incomplete strategy% (26331)------------------------------
% 0.21/0.56  % (26331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26331)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26331)Memory used [KB]: 10746
% 0.21/0.56  % (26331)Time elapsed: 0.146 s
% 0.21/0.56  % (26331)------------------------------
% 0.21/0.56  % (26331)------------------------------
% 0.21/0.56  % (26339)Refutation not found, incomplete strategy% (26339)------------------------------
% 0.21/0.56  % (26339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26341)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26341)Memory used [KB]: 6268
% 0.21/0.56  % (26341)Time elapsed: 0.136 s
% 0.21/0.56  % (26341)------------------------------
% 0.21/0.56  % (26341)------------------------------
% 1.61/0.56  % (26339)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.56  
% 1.61/0.56  % (26339)Memory used [KB]: 10746
% 1.61/0.56  % (26339)Time elapsed: 0.149 s
% 1.61/0.56  % (26339)------------------------------
% 1.61/0.56  % (26339)------------------------------
% 1.61/0.56  % SZS output start Proof for theBenchmark
% 1.61/0.56  fof(f531,plain,(
% 1.61/0.56    $false),
% 1.61/0.56    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f282,f301,f392,f416,f433,f528])).
% 1.61/0.56  fof(f528,plain,(
% 1.61/0.56    ~spl7_13),
% 1.61/0.56    inference(avatar_contradiction_clause,[],[f526])).
% 1.61/0.56  fof(f526,plain,(
% 1.61/0.56    $false | ~spl7_13),
% 1.61/0.56    inference(unit_resulting_resolution,[],[f152,f90,f177,f450])).
% 1.61/0.56  fof(f450,plain,(
% 1.61/0.56    ( ! [X0] : (sK3 != sK4(X0) | ~r2_hidden(sK3,X0) | k1_xboole_0 = X0) ) | ~spl7_13),
% 1.61/0.56    inference(superposition,[],[f58,f281])).
% 1.61/0.57  fof(f281,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | ~spl7_13),
% 1.61/0.57    inference(avatar_component_clause,[],[f279])).
% 1.61/0.57  fof(f279,plain,(
% 1.61/0.57    spl7_13 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.61/0.57  fof(f58,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f30])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.61/0.57    inference(ennf_transformation,[],[f12])).
% 1.61/0.57  fof(f12,axiom,(
% 1.61/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.61/0.57  fof(f177,plain,(
% 1.61/0.57    ( ! [X1] : (sK4(k1_tarski(X1)) = X1) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f126,f152])).
% 1.61/0.57  fof(f126,plain,(
% 1.61/0.57    ( ! [X1] : (sK4(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 1.61/0.57    inference(resolution,[],[f91,f56])).
% 1.61/0.57  fof(f56,plain,(
% 1.61/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f30])).
% 1.61/0.57  fof(f91,plain,(
% 1.61/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.61/0.57    inference(equality_resolution,[],[f74])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f40])).
% 1.61/0.57  fof(f40,plain,(
% 1.61/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.61/0.57    inference(rectify,[],[f37])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.61/0.57    inference(nnf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.61/0.57  fof(f90,plain,(
% 1.61/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.61/0.57    inference(equality_resolution,[],[f89])).
% 1.61/0.57  fof(f89,plain,(
% 1.61/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.61/0.57    inference(equality_resolution,[],[f75])).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f40])).
% 1.61/0.57  fof(f152,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.61/0.57    inference(superposition,[],[f141,f79])).
% 1.61/0.57  fof(f79,plain,(
% 1.61/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.57  fof(f141,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f139,f134])).
% 1.61/0.57  fof(f134,plain,(
% 1.61/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(trivial_inequality_removal,[],[f133])).
% 1.61/0.57  fof(f133,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(superposition,[],[f64,f52])).
% 1.61/0.57  fof(f52,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.61/0.57    inference(nnf_transformation,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.61/0.57  fof(f139,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1) | r2_hidden(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(superposition,[],[f53,f51])).
% 1.61/0.57  fof(f51,plain,(
% 1.61/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.61/0.57  fof(f53,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f28])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.61/0.57    inference(flattening,[],[f27])).
% 1.61/0.57  fof(f27,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.61/0.57    inference(nnf_transformation,[],[f8])).
% 1.61/0.57  fof(f8,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.61/0.57  fof(f433,plain,(
% 1.61/0.57    spl7_9 | ~spl7_2 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 1.61/0.57    inference(avatar_split_clause,[],[f432,f121,f116,f111,f106,f97,f211])).
% 1.61/0.57  fof(f211,plain,(
% 1.61/0.57    spl7_9 <=> sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.61/0.57  fof(f97,plain,(
% 1.61/0.57    spl7_2 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.61/0.57  fof(f106,plain,(
% 1.61/0.57    spl7_4 <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.61/0.57  fof(f111,plain,(
% 1.61/0.57    spl7_5 <=> k1_xboole_0 = sK2),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.61/0.57  fof(f116,plain,(
% 1.61/0.57    spl7_6 <=> k1_xboole_0 = sK1),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.61/0.57  fof(f121,plain,(
% 1.61/0.57    spl7_7 <=> k1_xboole_0 = sK0),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.61/0.57  fof(f432,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | (~spl7_2 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f431,f123])).
% 1.61/0.57  fof(f123,plain,(
% 1.61/0.57    k1_xboole_0 != sK0 | spl7_7),
% 1.61/0.57    inference(avatar_component_clause,[],[f121])).
% 1.61/0.57  fof(f431,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4 | spl7_5 | spl7_6)),
% 1.61/0.57    inference(subsumption_resolution,[],[f430,f118])).
% 1.61/0.57  fof(f118,plain,(
% 1.61/0.57    k1_xboole_0 != sK1 | spl7_6),
% 1.61/0.57    inference(avatar_component_clause,[],[f116])).
% 1.61/0.57  fof(f430,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4 | spl7_5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f429,f113])).
% 1.61/0.57  fof(f113,plain,(
% 1.61/0.57    k1_xboole_0 != sK2 | spl7_5),
% 1.61/0.57    inference(avatar_component_clause,[],[f111])).
% 1.61/0.57  fof(f429,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_2 | ~spl7_4)),
% 1.61/0.57    inference(subsumption_resolution,[],[f427,f108])).
% 1.61/0.57  fof(f108,plain,(
% 1.61/0.57    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl7_4),
% 1.61/0.57    inference(avatar_component_clause,[],[f106])).
% 1.61/0.57  fof(f427,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_2),
% 1.61/0.57    inference(superposition,[],[f49,f99])).
% 1.61/0.57  fof(f99,plain,(
% 1.61/0.57    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_2),
% 1.61/0.57    inference(avatar_component_clause,[],[f97])).
% 1.61/0.57  fof(f49,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.61/0.57    inference(ennf_transformation,[],[f13])).
% 1.61/0.57  fof(f13,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.61/0.57  fof(f416,plain,(
% 1.61/0.57    ~spl7_3 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 1.61/0.57    inference(avatar_contradiction_clause,[],[f415])).
% 1.61/0.57  fof(f415,plain,(
% 1.61/0.57    $false | (~spl7_3 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f414,f123])).
% 1.61/0.57  fof(f414,plain,(
% 1.61/0.57    k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4 | spl7_5 | spl7_6)),
% 1.61/0.57    inference(subsumption_resolution,[],[f413,f118])).
% 1.61/0.57  fof(f413,plain,(
% 1.61/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4 | spl7_5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f412,f113])).
% 1.61/0.57  fof(f412,plain,(
% 1.61/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4)),
% 1.61/0.57    inference(subsumption_resolution,[],[f411,f108])).
% 1.61/0.57  fof(f411,plain,(
% 1.61/0.57    ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f403,f149])).
% 1.61/0.57  fof(f149,plain,(
% 1.61/0.57    ( ! [X4,X5,X3] : (k3_mcart_1(X3,X4,X5) != X5) )),
% 1.61/0.57    inference(superposition,[],[f130,f63])).
% 1.61/0.57  fof(f63,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.61/0.57  fof(f130,plain,(
% 1.61/0.57    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.61/0.57    inference(forward_demodulation,[],[f80,f60])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,axiom,(
% 1.61/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.61/0.57  fof(f80,plain,(
% 1.61/0.57    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.61/0.57    inference(equality_resolution,[],[f62])).
% 1.61/0.57  fof(f62,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f22])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.61/0.57    inference(ennf_transformation,[],[f11])).
% 1.61/0.57  fof(f11,axiom,(
% 1.61/0.57    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.61/0.57  fof(f403,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),sK3) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_3),
% 1.61/0.57    inference(superposition,[],[f49,f103])).
% 1.61/0.57  fof(f103,plain,(
% 1.61/0.57    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_3),
% 1.61/0.57    inference(avatar_component_clause,[],[f101])).
% 1.61/0.57  fof(f101,plain,(
% 1.61/0.57    spl7_3 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.61/0.57  % (26343)Refutation not found, incomplete strategy% (26343)------------------------------
% 1.61/0.57  % (26343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  fof(f392,plain,(
% 1.61/0.57    ~spl7_11),
% 1.61/0.57    inference(avatar_contradiction_clause,[],[f390])).
% 1.61/0.57  fof(f390,plain,(
% 1.61/0.57    $false | ~spl7_11),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f152,f90,f177,f341])).
% 1.61/0.57  fof(f341,plain,(
% 1.61/0.57    ( ! [X1] : (sK3 != sK4(X1) | ~r2_hidden(sK3,X1) | k1_xboole_0 = X1) ) | ~spl7_11),
% 1.61/0.57    inference(superposition,[],[f57,f234])).
% 1.61/0.57  fof(f234,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_11),
% 1.61/0.57    inference(avatar_component_clause,[],[f232])).
% 1.61/0.57  fof(f232,plain,(
% 1.61/0.57    spl7_11 <=> sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.61/0.57  fof(f57,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f30])).
% 1.61/0.57  fof(f301,plain,(
% 1.61/0.57    spl7_11 | ~spl7_1 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7),
% 1.61/0.57    inference(avatar_split_clause,[],[f300,f121,f116,f111,f106,f93,f232])).
% 1.61/0.57  fof(f93,plain,(
% 1.61/0.57    spl7_1 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.61/0.57  fof(f300,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | (~spl7_1 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f299,f123])).
% 1.61/0.57  fof(f299,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4 | spl7_5 | spl7_6)),
% 1.61/0.57    inference(subsumption_resolution,[],[f298,f118])).
% 1.61/0.57  fof(f298,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4 | spl7_5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f297,f113])).
% 1.61/0.57  fof(f297,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_1 | ~spl7_4)),
% 1.61/0.57    inference(subsumption_resolution,[],[f290,f108])).
% 1.61/0.57  fof(f290,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(sK3,k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_1),
% 1.61/0.57    inference(superposition,[],[f49,f95])).
% 1.61/0.57  fof(f95,plain,(
% 1.61/0.57    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl7_1),
% 1.61/0.57    inference(avatar_component_clause,[],[f93])).
% 1.61/0.57  fof(f282,plain,(
% 1.61/0.57    spl7_13 | ~spl7_4 | spl7_5 | spl7_6 | spl7_7 | ~spl7_9),
% 1.61/0.57    inference(avatar_split_clause,[],[f277,f211,f121,f116,f111,f106,f279])).
% 1.61/0.57  fof(f277,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | (~spl7_4 | spl7_5 | spl7_6 | spl7_7 | ~spl7_9)),
% 1.61/0.57    inference(subsumption_resolution,[],[f276,f123])).
% 1.61/0.57  fof(f276,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK0 | (~spl7_4 | spl7_5 | spl7_6 | ~spl7_9)),
% 1.61/0.57    inference(subsumption_resolution,[],[f275,f118])).
% 1.61/0.57  fof(f275,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_4 | spl7_5 | ~spl7_9)),
% 1.61/0.57    inference(subsumption_resolution,[],[f274,f113])).
% 1.61/0.57  fof(f274,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_9)),
% 1.61/0.57    inference(subsumption_resolution,[],[f259,f108])).
% 1.61/0.57  fof(f259,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k2_mcart_1(sK3)) | ~m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_9),
% 1.61/0.57    inference(superposition,[],[f213,f48])).
% 1.61/0.57  fof(f48,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.61/0.57    inference(ennf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.61/0.57  fof(f213,plain,(
% 1.61/0.57    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK3,k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl7_9),
% 1.61/0.57    inference(avatar_component_clause,[],[f211])).
% 1.61/0.57  fof(f124,plain,(
% 1.61/0.57    ~spl7_7),
% 1.61/0.57    inference(avatar_split_clause,[],[f41,f121])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    k1_xboole_0 != sK0),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) => ((sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.57    inference(ennf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,negated_conjecture,(
% 1.61/0.57    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.57    inference(negated_conjecture,[],[f16])).
% 1.61/0.57  fof(f16,conjecture,(
% 1.61/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.61/0.57  fof(f119,plain,(
% 1.61/0.57    ~spl7_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f42,f116])).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    k1_xboole_0 != sK1),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f114,plain,(
% 1.61/0.57    ~spl7_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f43,f111])).
% 1.61/0.57  fof(f43,plain,(
% 1.61/0.57    k1_xboole_0 != sK2),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f109,plain,(
% 1.61/0.57    spl7_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f44,f106])).
% 1.61/0.57  fof(f44,plain,(
% 1.61/0.57    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f104,plain,(
% 1.61/0.57    spl7_1 | spl7_2 | spl7_3),
% 1.61/0.57    inference(avatar_split_clause,[],[f45,f101,f97,f93])).
% 1.61/0.57  fof(f45,plain,(
% 1.61/0.57    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (26336)------------------------------
% 1.61/0.57  % (26336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (26336)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (26336)Memory used [KB]: 6524
% 1.61/0.57  % (26336)Time elapsed: 0.135 s
% 1.61/0.57  % (26336)------------------------------
% 1.61/0.57  % (26336)------------------------------
% 1.61/0.57  % (26314)Success in time 0.209 s
%------------------------------------------------------------------------------
