%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:29 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 139 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  285 ( 364 expanded)
%              Number of equality atoms :   89 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f435,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f96,f342,f349,f377,f395,f434])).

fof(f434,plain,
    ( spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl6_7
    | spl6_9 ),
    inference(subsumption_resolution,[],[f431,f375])).

fof(f375,plain,
    ( sK0 != sK1
    | spl6_9 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_9
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f431,plain,
    ( sK0 = sK1
    | spl6_7 ),
    inference(trivial_inequality_removal,[],[f430])).

fof(f430,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | sK0 = sK1
    | spl6_7 ),
    inference(superposition,[],[f341,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f341,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl6_7
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f395,plain,
    ( spl6_1
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f393,f58])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f393,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl6_1
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f392,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f392,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0)))
    | spl6_1
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f388,f58])).

fof(f388,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0)))
    | spl6_1
    | ~ spl6_9 ),
    inference(superposition,[],[f85,f376])).

fof(f376,plain,
    ( sK0 = sK1
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f374])).

fof(f85,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_1
  <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f377,plain,
    ( spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f371,f255,f374])).

fof(f255,plain,
    ( spl6_5
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f371,plain,
    ( sK0 = sK1
    | ~ spl6_5 ),
    inference(resolution,[],[f256,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f256,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f255])).

fof(f349,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f345,f257])).

fof(f257,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f255])).

fof(f345,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | spl6_6 ),
    inference(resolution,[],[f337,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f337,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl6_6
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f342,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_2 ),
    inference(avatar_split_clause,[],[f329,f93,f339,f335])).

fof(f93,plain,
    ( spl6_2
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f329,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl6_2 ),
    inference(superposition,[],[f95,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f60,f277])).

fof(f277,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f193,f242])).

fof(f242,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f239,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f239,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f119,f91])).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f89,f51])).

fof(f89,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f58])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f60,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f193,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f75,f159])).

fof(f159,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f155,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f68,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f155,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_xboole_0)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f74,f147])).

fof(f147,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f146,f62])).

fof(f146,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f66,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f95,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f90,f83,f93])).

fof(f90,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl6_1 ),
    inference(superposition,[],[f85,f50])).

fof(f86,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (32329)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (32325)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (32325)Refutation not found, incomplete strategy% (32325)------------------------------
% 0.21/0.49  % (32325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32325)Memory used [KB]: 1663
% 0.21/0.49  % (32325)Time elapsed: 0.082 s
% 0.21/0.49  % (32325)------------------------------
% 0.21/0.49  % (32325)------------------------------
% 0.21/0.50  % (32336)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (32333)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (32353)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (32332)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (32336)Refutation not found, incomplete strategy% (32336)------------------------------
% 0.21/0.50  % (32336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32336)Memory used [KB]: 10618
% 0.21/0.50  % (32336)Time elapsed: 0.096 s
% 0.21/0.50  % (32336)------------------------------
% 0.21/0.50  % (32336)------------------------------
% 0.21/0.50  % (32333)Refutation not found, incomplete strategy% (32333)------------------------------
% 0.21/0.50  % (32333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32345)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (32333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32333)Memory used [KB]: 10618
% 0.21/0.51  % (32333)Time elapsed: 0.093 s
% 0.21/0.51  % (32333)------------------------------
% 0.21/0.51  % (32333)------------------------------
% 0.21/0.51  % (32349)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (32345)Refutation not found, incomplete strategy% (32345)------------------------------
% 0.21/0.51  % (32345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32345)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32345)Memory used [KB]: 10746
% 0.21/0.51  % (32345)Time elapsed: 0.115 s
% 0.21/0.51  % (32345)------------------------------
% 0.21/0.51  % (32345)------------------------------
% 0.21/0.51  % (32335)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (32330)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (32334)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (32341)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (32335)Refutation not found, incomplete strategy% (32335)------------------------------
% 0.21/0.51  % (32335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32335)Memory used [KB]: 10618
% 0.21/0.51  % (32335)Time elapsed: 0.106 s
% 0.21/0.51  % (32335)------------------------------
% 0.21/0.51  % (32335)------------------------------
% 0.21/0.51  % (32334)Refutation not found, incomplete strategy% (32334)------------------------------
% 0.21/0.51  % (32334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32334)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32334)Memory used [KB]: 10618
% 0.21/0.51  % (32334)Time elapsed: 0.106 s
% 0.21/0.51  % (32334)------------------------------
% 0.21/0.51  % (32334)------------------------------
% 0.21/0.52  % (32328)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (32338)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (32346)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (32346)Refutation not found, incomplete strategy% (32346)------------------------------
% 0.21/0.53  % (32346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32346)Memory used [KB]: 1663
% 0.21/0.53  % (32346)Time elapsed: 0.096 s
% 0.21/0.53  % (32346)------------------------------
% 0.21/0.53  % (32346)------------------------------
% 0.21/0.53  % (32327)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32326)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (32327)Refutation not found, incomplete strategy% (32327)------------------------------
% 0.21/0.53  % (32327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32327)Memory used [KB]: 10746
% 0.21/0.53  % (32327)Time elapsed: 0.127 s
% 0.21/0.53  % (32327)------------------------------
% 0.21/0.53  % (32327)------------------------------
% 0.21/0.53  % (32352)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (32348)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (32354)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (32348)Refutation not found, incomplete strategy% (32348)------------------------------
% 0.21/0.53  % (32348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32348)Memory used [KB]: 1791
% 0.21/0.53  % (32348)Time elapsed: 0.099 s
% 0.21/0.53  % (32348)------------------------------
% 0.21/0.53  % (32348)------------------------------
% 0.21/0.54  % (32344)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (32351)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32350)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (32339)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.54  % (32343)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (32347)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.55  % (32342)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (32337)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.55  % (32342)Refutation not found, incomplete strategy% (32342)------------------------------
% 1.50/0.55  % (32342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (32342)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (32342)Memory used [KB]: 10618
% 1.50/0.55  % (32342)Time elapsed: 0.149 s
% 1.50/0.55  % (32342)------------------------------
% 1.50/0.55  % (32342)------------------------------
% 1.50/0.55  % (32340)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.55  % (32331)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.10/0.63  % (32355)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.64  % (32356)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.64  % (32358)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.64  % (32357)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.64  % (32360)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.10/0.64  % (32359)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.44/0.67  % (32362)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.44/0.67  % (32359)Refutation found. Thanks to Tanya!
% 2.44/0.67  % SZS status Theorem for theBenchmark
% 2.44/0.67  % SZS output start Proof for theBenchmark
% 2.44/0.67  fof(f435,plain,(
% 2.44/0.67    $false),
% 2.44/0.67    inference(avatar_sat_refutation,[],[f86,f96,f342,f349,f377,f395,f434])).
% 2.44/0.67  fof(f434,plain,(
% 2.44/0.67    spl6_7 | spl6_9),
% 2.44/0.67    inference(avatar_contradiction_clause,[],[f433])).
% 2.44/0.67  fof(f433,plain,(
% 2.44/0.67    $false | (spl6_7 | spl6_9)),
% 2.44/0.67    inference(subsumption_resolution,[],[f431,f375])).
% 2.44/0.67  fof(f375,plain,(
% 2.44/0.67    sK0 != sK1 | spl6_9),
% 2.44/0.67    inference(avatar_component_clause,[],[f374])).
% 2.44/0.67  fof(f374,plain,(
% 2.44/0.67    spl6_9 <=> sK0 = sK1),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 2.44/0.67  fof(f431,plain,(
% 2.44/0.67    sK0 = sK1 | spl6_7),
% 2.44/0.67    inference(trivial_inequality_removal,[],[f430])).
% 2.44/0.67  fof(f430,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | sK0 = sK1 | spl6_7),
% 2.44/0.67    inference(superposition,[],[f341,f59])).
% 2.44/0.67  fof(f59,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.44/0.67    inference(cnf_transformation,[],[f28])).
% 2.44/0.67  fof(f28,plain,(
% 2.44/0.67    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 2.44/0.67    inference(ennf_transformation,[],[f20])).
% 2.44/0.67  fof(f20,axiom,(
% 2.44/0.67    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 2.44/0.67  fof(f341,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl6_7),
% 2.44/0.67    inference(avatar_component_clause,[],[f339])).
% 2.44/0.67  fof(f339,plain,(
% 2.44/0.67    spl6_7 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.44/0.67  fof(f395,plain,(
% 2.44/0.67    spl6_1 | ~spl6_9),
% 2.44/0.67    inference(avatar_contradiction_clause,[],[f394])).
% 2.44/0.67  fof(f394,plain,(
% 2.44/0.67    $false | (spl6_1 | ~spl6_9)),
% 2.44/0.67    inference(subsumption_resolution,[],[f393,f58])).
% 2.44/0.67  fof(f58,plain,(
% 2.44/0.67    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f11])).
% 2.44/0.67  fof(f11,axiom,(
% 2.44/0.67    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.44/0.67  fof(f393,plain,(
% 2.44/0.67    k1_tarski(sK0) != k2_tarski(sK0,sK0) | (spl6_1 | ~spl6_9)),
% 2.44/0.67    inference(forward_demodulation,[],[f392,f51])).
% 2.44/0.67  fof(f51,plain,(
% 2.44/0.67    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.44/0.67    inference(cnf_transformation,[],[f21])).
% 2.44/0.67  fof(f21,axiom,(
% 2.44/0.67    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.44/0.67  fof(f392,plain,(
% 2.44/0.67    k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0))) | (spl6_1 | ~spl6_9)),
% 2.44/0.67    inference(forward_demodulation,[],[f388,f58])).
% 2.44/0.67  fof(f388,plain,(
% 2.44/0.67    k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0))) | (spl6_1 | ~spl6_9)),
% 2.44/0.67    inference(superposition,[],[f85,f376])).
% 2.44/0.67  fof(f376,plain,(
% 2.44/0.67    sK0 = sK1 | ~spl6_9),
% 2.44/0.67    inference(avatar_component_clause,[],[f374])).
% 2.44/0.67  fof(f85,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) | spl6_1),
% 2.44/0.67    inference(avatar_component_clause,[],[f83])).
% 2.44/0.67  fof(f83,plain,(
% 2.44/0.67    spl6_1 <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.44/0.67  fof(f377,plain,(
% 2.44/0.67    spl6_9 | ~spl6_5),
% 2.44/0.67    inference(avatar_split_clause,[],[f371,f255,f374])).
% 2.44/0.67  fof(f255,plain,(
% 2.44/0.67    spl6_5 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.44/0.67  fof(f371,plain,(
% 2.44/0.67    sK0 = sK1 | ~spl6_5),
% 2.44/0.67    inference(resolution,[],[f256,f79])).
% 2.44/0.67  fof(f79,plain,(
% 2.44/0.67    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 2.44/0.67    inference(equality_resolution,[],[f52])).
% 2.44/0.67  fof(f52,plain,(
% 2.44/0.67    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.44/0.67    inference(cnf_transformation,[],[f37])).
% 2.44/0.67  fof(f37,plain,(
% 2.44/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.44/0.67  fof(f36,plain,(
% 2.44/0.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.44/0.67    introduced(choice_axiom,[])).
% 2.44/0.67  fof(f35,plain,(
% 2.44/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.67    inference(rectify,[],[f34])).
% 2.44/0.67  fof(f34,plain,(
% 2.44/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.44/0.67    inference(nnf_transformation,[],[f10])).
% 2.44/0.67  fof(f10,axiom,(
% 2.44/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.44/0.67  fof(f256,plain,(
% 2.44/0.67    r2_hidden(sK1,k1_tarski(sK0)) | ~spl6_5),
% 2.44/0.67    inference(avatar_component_clause,[],[f255])).
% 2.44/0.67  fof(f349,plain,(
% 2.44/0.67    spl6_5 | spl6_6),
% 2.44/0.67    inference(avatar_contradiction_clause,[],[f348])).
% 2.44/0.67  fof(f348,plain,(
% 2.44/0.67    $false | (spl6_5 | spl6_6)),
% 2.44/0.67    inference(subsumption_resolution,[],[f345,f257])).
% 2.44/0.67  fof(f257,plain,(
% 2.44/0.67    ~r2_hidden(sK1,k1_tarski(sK0)) | spl6_5),
% 2.44/0.67    inference(avatar_component_clause,[],[f255])).
% 2.44/0.67  fof(f345,plain,(
% 2.44/0.67    r2_hidden(sK1,k1_tarski(sK0)) | spl6_6),
% 2.44/0.67    inference(resolution,[],[f337,f56])).
% 2.44/0.67  fof(f56,plain,(
% 2.44/0.67    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f27])).
% 2.44/0.67  fof(f27,plain,(
% 2.44/0.67    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.44/0.67    inference(ennf_transformation,[],[f17])).
% 2.44/0.67  fof(f17,axiom,(
% 2.44/0.67    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.44/0.67  fof(f337,plain,(
% 2.44/0.67    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl6_6),
% 2.44/0.67    inference(avatar_component_clause,[],[f335])).
% 2.44/0.67  fof(f335,plain,(
% 2.44/0.67    spl6_6 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.44/0.67  fof(f342,plain,(
% 2.44/0.67    ~spl6_6 | ~spl6_7 | spl6_2),
% 2.44/0.67    inference(avatar_split_clause,[],[f329,f93,f339,f335])).
% 2.44/0.67  fof(f93,plain,(
% 2.44/0.67    spl6_2 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.44/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.44/0.67  fof(f329,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl6_2),
% 2.44/0.67    inference(superposition,[],[f95,f282])).
% 2.44/0.67  fof(f282,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.67    inference(superposition,[],[f60,f277])).
% 2.44/0.67  fof(f277,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.67    inference(forward_demodulation,[],[f193,f242])).
% 2.44/0.67  fof(f242,plain,(
% 2.44/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.44/0.67    inference(subsumption_resolution,[],[f239,f80])).
% 2.44/0.67  fof(f80,plain,(
% 2.44/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.44/0.67    inference(equality_resolution,[],[f73])).
% 2.44/0.67  fof(f73,plain,(
% 2.44/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.44/0.67    inference(cnf_transformation,[],[f48])).
% 2.44/0.67  fof(f48,plain,(
% 2.44/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.67    inference(flattening,[],[f47])).
% 2.44/0.67  fof(f47,plain,(
% 2.44/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.44/0.67    inference(nnf_transformation,[],[f5])).
% 2.44/0.67  fof(f5,axiom,(
% 2.44/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.44/0.67  fof(f239,plain,(
% 2.44/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0 | ~r1_tarski(X0,X0)) )),
% 2.44/0.67    inference(superposition,[],[f119,f91])).
% 2.44/0.67  fof(f91,plain,(
% 2.44/0.67    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.44/0.67    inference(forward_demodulation,[],[f89,f51])).
% 2.44/0.67  fof(f89,plain,(
% 2.44/0.67    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 2.44/0.67    inference(superposition,[],[f50,f58])).
% 2.44/0.67  fof(f50,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.44/0.67    inference(cnf_transformation,[],[f18])).
% 2.44/0.67  fof(f18,axiom,(
% 2.44/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.44/0.67  fof(f119,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 2.44/0.67    inference(superposition,[],[f60,f71])).
% 2.44/0.67  fof(f71,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f46])).
% 2.44/0.67  fof(f46,plain,(
% 2.44/0.67    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.44/0.67    inference(nnf_transformation,[],[f6])).
% 2.44/0.67  fof(f6,axiom,(
% 2.44/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.44/0.67  fof(f193,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.67    inference(superposition,[],[f75,f159])).
% 2.44/0.67  fof(f159,plain,(
% 2.44/0.67    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 2.44/0.67    inference(resolution,[],[f155,f102])).
% 2.44/0.67  fof(f102,plain,(
% 2.44/0.67    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.67    inference(resolution,[],[f68,f62])).
% 2.44/0.67  fof(f62,plain,(
% 2.44/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f41])).
% 2.44/0.67  fof(f41,plain,(
% 2.44/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.44/0.67  fof(f40,plain,(
% 2.44/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.44/0.67    introduced(choice_axiom,[])).
% 2.44/0.67  fof(f39,plain,(
% 2.44/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.67    inference(rectify,[],[f38])).
% 2.44/0.67  fof(f38,plain,(
% 2.44/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.67    inference(nnf_transformation,[],[f29])).
% 2.44/0.67  fof(f29,plain,(
% 2.44/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/0.67    inference(ennf_transformation,[],[f2])).
% 2.44/0.67  fof(f2,axiom,(
% 2.44/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.44/0.67  fof(f68,plain,(
% 2.44/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f45])).
% 2.44/0.67  fof(f45,plain,(
% 2.44/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f44])).
% 2.44/0.67  fof(f44,plain,(
% 2.44/0.67    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.44/0.67    introduced(choice_axiom,[])).
% 2.44/0.67  fof(f31,plain,(
% 2.44/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(ennf_transformation,[],[f25])).
% 2.44/0.67  fof(f25,plain,(
% 2.44/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(rectify,[],[f4])).
% 2.44/0.67  fof(f4,axiom,(
% 2.44/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.44/0.67  fof(f155,plain,(
% 2.44/0.67    ( ! [X7] : (~r1_tarski(X7,k1_xboole_0) | k1_xboole_0 = X7) )),
% 2.44/0.67    inference(resolution,[],[f74,f147])).
% 2.44/0.67  fof(f147,plain,(
% 2.44/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.44/0.67    inference(resolution,[],[f146,f62])).
% 2.44/0.67  fof(f146,plain,(
% 2.44/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.44/0.67    inference(condensation,[],[f136])).
% 2.44/0.67  fof(f136,plain,(
% 2.44/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 2.44/0.67    inference(resolution,[],[f66,f69])).
% 2.44/0.67  fof(f69,plain,(
% 2.44/0.67    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f8])).
% 2.44/0.67  fof(f8,axiom,(
% 2.44/0.67    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.44/0.67  fof(f66,plain,(
% 2.44/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f43])).
% 2.44/0.67  fof(f43,plain,(
% 2.44/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f42])).
% 2.44/0.67  fof(f42,plain,(
% 2.44/0.67    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.44/0.67    introduced(choice_axiom,[])).
% 2.44/0.67  fof(f30,plain,(
% 2.44/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(ennf_transformation,[],[f24])).
% 2.44/0.67  fof(f24,plain,(
% 2.44/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.67    inference(rectify,[],[f3])).
% 2.44/0.67  fof(f3,axiom,(
% 2.44/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.44/0.67  fof(f74,plain,(
% 2.44/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.44/0.67    inference(cnf_transformation,[],[f48])).
% 2.44/0.67  fof(f75,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.44/0.67    inference(cnf_transformation,[],[f7])).
% 2.44/0.67  fof(f7,axiom,(
% 2.44/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.44/0.67  fof(f60,plain,(
% 2.44/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.44/0.67    inference(cnf_transformation,[],[f9])).
% 2.44/0.67  fof(f9,axiom,(
% 2.44/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.44/0.67  fof(f95,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl6_2),
% 2.44/0.67    inference(avatar_component_clause,[],[f93])).
% 2.44/0.67  fof(f96,plain,(
% 2.44/0.67    ~spl6_2 | spl6_1),
% 2.44/0.67    inference(avatar_split_clause,[],[f90,f83,f93])).
% 2.44/0.67  fof(f90,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl6_1),
% 2.44/0.67    inference(superposition,[],[f85,f50])).
% 2.44/0.67  fof(f86,plain,(
% 2.44/0.67    ~spl6_1),
% 2.44/0.67    inference(avatar_split_clause,[],[f49,f83])).
% 2.44/0.67  fof(f49,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.44/0.67    inference(cnf_transformation,[],[f33])).
% 2.44/0.67  fof(f33,plain,(
% 2.44/0.67    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.44/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 2.44/0.67  fof(f32,plain,(
% 2.44/0.67    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.44/0.67    introduced(choice_axiom,[])).
% 2.44/0.67  fof(f26,plain,(
% 2.44/0.67    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.67    inference(ennf_transformation,[],[f23])).
% 2.44/0.67  fof(f23,negated_conjecture,(
% 2.44/0.67    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.67    inference(negated_conjecture,[],[f22])).
% 2.44/0.67  fof(f22,conjecture,(
% 2.44/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.44/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 2.44/0.67  % SZS output end Proof for theBenchmark
% 2.44/0.67  % (32359)------------------------------
% 2.44/0.67  % (32359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.67  % (32359)Termination reason: Refutation
% 2.44/0.67  
% 2.44/0.67  % (32359)Memory used [KB]: 11001
% 2.44/0.67  % (32359)Time elapsed: 0.138 s
% 2.44/0.67  % (32359)------------------------------
% 2.44/0.67  % (32359)------------------------------
% 2.44/0.68  % (32324)Success in time 0.32 s
%------------------------------------------------------------------------------
