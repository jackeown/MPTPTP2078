%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:29 EST 2020

% Result     : Theorem 5.55s
% Output     : Refutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 170 expanded)
%              Number of leaves         :   24 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 ( 569 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f93,f237,f353,f487,f505,f526,f557,f563])).

fof(f563,plain,
    ( spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f560,f352])).

fof(f352,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_7
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f560,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f483,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f483,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl6_8
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f557,plain,
    ( spl6_6
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | spl6_6
    | spl6_13 ),
    inference(subsumption_resolution,[],[f554,f236])).

fof(f236,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl6_6
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f554,plain,
    ( r2_hidden(sK3,sK1)
    | spl6_13 ),
    inference(resolution,[],[f525,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f525,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),sK1)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl6_13
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f526,plain,
    ( ~ spl6_13
    | spl6_10 ),
    inference(avatar_split_clause,[],[f510,f500,f523])).

fof(f500,plain,
    ( spl6_10
  <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f510,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),sK1)
    | spl6_10 ),
    inference(resolution,[],[f502,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f43,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f502,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f500])).

fof(f505,plain,
    ( spl6_8
    | ~ spl6_10
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f504,f485,f500,f481])).

fof(f485,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK1),X0)
        | ~ r1_xboole_0(k1_tarski(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f504,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))
    | r1_xboole_0(sK0,sK1)
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f494,f61])).

fof(f494,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK0))
    | r1_xboole_0(sK0,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f486,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f50,f61])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f486,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK1),X0)
        | ~ r1_xboole_0(k1_tarski(sK3),X0) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f485])).

fof(f487,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f474,f83,f485,f481])).

fof(f83,plain,
    ( spl6_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK1),X0)
        | ~ r1_xboole_0(k1_tarski(sK3),X0)
        | r1_xboole_0(sK0,sK1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f290,f50])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(sK0,sK1))
        | ~ r2_hidden(X1,X0)
        | ~ r1_xboole_0(k1_tarski(sK3),X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f211,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f211,plain,
    ( ! [X0] :
        ( r1_xboole_0(k3_xboole_0(sK0,sK1),X0)
        | ~ r1_xboole_0(k1_tarski(sK3),X0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f112,f85])).

fof(f85,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f353,plain,
    ( ~ spl6_7
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f348,f90,f68,f350])).

fof(f68,plain,
    ( spl6_1
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f90,plain,
    ( spl6_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f348,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f342,f92])).

fof(f92,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f342,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl6_1 ),
    inference(resolution,[],[f152,f70])).

fof(f70,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f152,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k2_xboole_0(X7,X8),X6)
      | ~ r1_xboole_0(X6,X8)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f40,f48])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f237,plain,
    ( ~ spl6_6
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f231,f90,f78,f234])).

fof(f78,plain,
    ( spl6_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f231,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f229,f80])).

fof(f80,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f229,plain,
    ( ! [X60] :
        ( ~ r2_hidden(X60,sK2)
        | ~ r2_hidden(X60,sK1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f124,f92])).

fof(f93,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f87,f73,f90])).

fof(f73,plain,
    ( spl6_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f87,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f48,f75])).

fof(f75,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f86,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f26])).

fof(f26,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f81,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:42:54 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.45  % (22508)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.45  % (22516)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.46  % (22513)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (22505)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.50  % (22503)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (22528)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.52  % (22521)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.52  % (22514)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.53  % (22506)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.54  % (22529)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.54  % (22523)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.54  % (22515)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.54  % (22504)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.54  % (22522)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.55  % (22523)Refutation not found, incomplete strategy% (22523)------------------------------
% 0.18/0.55  % (22523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.55  % (22523)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.55  
% 0.18/0.55  % (22523)Memory used [KB]: 10746
% 0.18/0.55  % (22523)Time elapsed: 0.119 s
% 0.18/0.55  % (22523)------------------------------
% 0.18/0.55  % (22523)------------------------------
% 0.18/0.55  % (22507)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.55  % (22512)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.61/0.56  % (22520)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.56  % (22530)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.56  % (22524)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.61/0.57  % (22511)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.82/0.58  % (22501)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.82/0.58  % (22518)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.82/0.58  % (22519)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.82/0.59  % (22517)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.82/0.59  % (22502)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.82/0.59  % (22509)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.82/0.61  % (22527)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.62  % (22526)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.82/0.63  % (22510)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.64  % (22525)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.94/0.73  % (22555)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.04/0.80  % (22506)Time limit reached!
% 3.04/0.80  % (22506)------------------------------
% 3.04/0.80  % (22506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.80  % (22506)Termination reason: Time limit
% 3.04/0.80  % (22506)Termination phase: Saturation
% 3.04/0.80  
% 3.04/0.80  % (22506)Memory used [KB]: 8315
% 3.04/0.80  % (22506)Time elapsed: 0.400 s
% 3.04/0.80  % (22506)------------------------------
% 3.04/0.80  % (22506)------------------------------
% 4.03/0.89  % (22513)Time limit reached!
% 4.03/0.89  % (22513)------------------------------
% 4.03/0.89  % (22513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.89  % (22513)Termination reason: Time limit
% 4.03/0.89  
% 4.03/0.89  % (22513)Memory used [KB]: 9083
% 4.03/0.89  % (22513)Time elapsed: 0.513 s
% 4.03/0.89  % (22513)------------------------------
% 4.03/0.89  % (22513)------------------------------
% 4.03/0.90  % (22502)Time limit reached!
% 4.03/0.90  % (22502)------------------------------
% 4.03/0.90  % (22502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.90  % (22502)Termination reason: Time limit
% 4.03/0.90  
% 4.03/0.90  % (22502)Memory used [KB]: 6396
% 4.03/0.90  % (22502)Time elapsed: 0.505 s
% 4.03/0.90  % (22502)------------------------------
% 4.03/0.90  % (22502)------------------------------
% 4.03/0.91  % (22501)Time limit reached!
% 4.03/0.91  % (22501)------------------------------
% 4.03/0.91  % (22501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (22501)Termination reason: Time limit
% 4.03/0.91  
% 4.03/0.91  % (22501)Memory used [KB]: 3454
% 4.03/0.91  % (22501)Time elapsed: 0.513 s
% 4.03/0.91  % (22501)------------------------------
% 4.03/0.91  % (22501)------------------------------
% 4.03/0.91  % (22518)Time limit reached!
% 4.03/0.91  % (22518)------------------------------
% 4.03/0.91  % (22518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.91  % (22518)Termination reason: Time limit
% 4.03/0.91  
% 4.03/0.91  % (22518)Memory used [KB]: 12409
% 4.03/0.91  % (22518)Time elapsed: 0.522 s
% 4.03/0.91  % (22518)------------------------------
% 4.03/0.91  % (22518)------------------------------
% 4.03/0.92  % (22511)Time limit reached!
% 4.03/0.92  % (22511)------------------------------
% 4.03/0.92  % (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.93  % (22511)Termination reason: Time limit
% 4.03/0.93  
% 4.03/0.93  % (22511)Memory used [KB]: 14328
% 4.03/0.93  % (22511)Time elapsed: 0.527 s
% 4.03/0.93  % (22511)------------------------------
% 4.03/0.93  % (22511)------------------------------
% 4.84/0.98  % (22556)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.84/1.00  % (22529)Time limit reached!
% 4.84/1.00  % (22529)------------------------------
% 4.84/1.00  % (22529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.00  % (22529)Termination reason: Time limit
% 4.84/1.00  % (22529)Termination phase: Saturation
% 4.84/1.00  
% 4.84/1.00  % (22529)Memory used [KB]: 8315
% 4.84/1.00  % (22529)Time elapsed: 0.600 s
% 4.84/1.00  % (22529)------------------------------
% 4.84/1.00  % (22529)------------------------------
% 4.84/1.00  % (22517)Time limit reached!
% 4.84/1.00  % (22517)------------------------------
% 4.84/1.00  % (22517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.00  % (22517)Termination reason: Time limit
% 4.84/1.00  
% 4.84/1.00  % (22517)Memory used [KB]: 14200
% 4.84/1.00  % (22517)Time elapsed: 0.604 s
% 4.84/1.00  % (22517)------------------------------
% 4.84/1.00  % (22517)------------------------------
% 4.84/1.02  % (22508)Time limit reached!
% 4.84/1.02  % (22508)------------------------------
% 4.84/1.02  % (22508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.02  % (22508)Termination reason: Time limit
% 4.84/1.02  
% 4.84/1.02  % (22508)Memory used [KB]: 10362
% 4.84/1.02  % (22508)Time elapsed: 0.631 s
% 4.84/1.02  % (22508)------------------------------
% 4.84/1.02  % (22508)------------------------------
% 5.08/1.06  % (22557)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.55/1.09  % (22557)Refutation found. Thanks to Tanya!
% 5.55/1.09  % SZS status Theorem for theBenchmark
% 5.55/1.09  % SZS output start Proof for theBenchmark
% 5.55/1.09  fof(f564,plain,(
% 5.55/1.09    $false),
% 5.55/1.09    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f93,f237,f353,f487,f505,f526,f557,f563])).
% 5.55/1.09  fof(f563,plain,(
% 5.55/1.09    spl6_7 | ~spl6_8),
% 5.55/1.09    inference(avatar_contradiction_clause,[],[f562])).
% 5.55/1.09  fof(f562,plain,(
% 5.55/1.09    $false | (spl6_7 | ~spl6_8)),
% 5.55/1.09    inference(subsumption_resolution,[],[f560,f352])).
% 5.55/1.09  fof(f352,plain,(
% 5.55/1.09    ~r1_xboole_0(sK1,sK0) | spl6_7),
% 5.55/1.09    inference(avatar_component_clause,[],[f350])).
% 5.55/1.09  fof(f350,plain,(
% 5.55/1.09    spl6_7 <=> r1_xboole_0(sK1,sK0)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 5.55/1.09  fof(f560,plain,(
% 5.55/1.09    r1_xboole_0(sK1,sK0) | ~spl6_8),
% 5.55/1.09    inference(resolution,[],[f483,f48])).
% 5.55/1.09  fof(f48,plain,(
% 5.55/1.09    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f23])).
% 5.55/1.09  fof(f23,plain,(
% 5.55/1.09    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 5.55/1.09    inference(ennf_transformation,[],[f3])).
% 5.55/1.09  fof(f3,axiom,(
% 5.55/1.09    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 5.55/1.09  fof(f483,plain,(
% 5.55/1.09    r1_xboole_0(sK0,sK1) | ~spl6_8),
% 5.55/1.09    inference(avatar_component_clause,[],[f481])).
% 5.55/1.09  fof(f481,plain,(
% 5.55/1.09    spl6_8 <=> r1_xboole_0(sK0,sK1)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 5.55/1.09  fof(f557,plain,(
% 5.55/1.09    spl6_6 | spl6_13),
% 5.55/1.09    inference(avatar_contradiction_clause,[],[f556])).
% 5.55/1.09  fof(f556,plain,(
% 5.55/1.09    $false | (spl6_6 | spl6_13)),
% 5.55/1.09    inference(subsumption_resolution,[],[f554,f236])).
% 5.55/1.09  fof(f236,plain,(
% 5.55/1.09    ~r2_hidden(sK3,sK1) | spl6_6),
% 5.55/1.09    inference(avatar_component_clause,[],[f234])).
% 5.55/1.09  fof(f234,plain,(
% 5.55/1.09    spl6_6 <=> r2_hidden(sK3,sK1)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 5.55/1.09  fof(f554,plain,(
% 5.55/1.09    r2_hidden(sK3,sK1) | spl6_13),
% 5.55/1.09    inference(resolution,[],[f525,f49])).
% 5.55/1.09  fof(f49,plain,(
% 5.55/1.09    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f24])).
% 5.55/1.09  fof(f24,plain,(
% 5.55/1.09    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 5.55/1.09    inference(ennf_transformation,[],[f14])).
% 5.55/1.09  fof(f14,axiom,(
% 5.55/1.09    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 5.55/1.09  fof(f525,plain,(
% 5.55/1.09    ~r1_xboole_0(k1_tarski(sK3),sK1) | spl6_13),
% 5.55/1.09    inference(avatar_component_clause,[],[f523])).
% 5.55/1.09  fof(f523,plain,(
% 5.55/1.09    spl6_13 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 5.55/1.09  fof(f526,plain,(
% 5.55/1.09    ~spl6_13 | spl6_10),
% 5.55/1.09    inference(avatar_split_clause,[],[f510,f500,f523])).
% 5.55/1.09  fof(f500,plain,(
% 5.55/1.09    spl6_10 <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 5.55/1.09  fof(f510,plain,(
% 5.55/1.09    ~r1_xboole_0(k1_tarski(sK3),sK1) | spl6_10),
% 5.55/1.09    inference(resolution,[],[f502,f106])).
% 5.55/1.09  fof(f106,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X2,X0)) )),
% 5.55/1.09    inference(superposition,[],[f43,f61])).
% 5.55/1.09  fof(f61,plain,(
% 5.55/1.09    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f1])).
% 5.55/1.09  fof(f1,axiom,(
% 5.55/1.09    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.55/1.09  fof(f43,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f21])).
% 5.55/1.09  fof(f21,plain,(
% 5.55/1.09    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 5.55/1.09    inference(ennf_transformation,[],[f8])).
% 5.55/1.09  fof(f8,axiom,(
% 5.55/1.09    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 5.55/1.09  fof(f502,plain,(
% 5.55/1.09    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | spl6_10),
% 5.55/1.09    inference(avatar_component_clause,[],[f500])).
% 5.55/1.09  fof(f505,plain,(
% 5.55/1.09    spl6_8 | ~spl6_10 | ~spl6_9),
% 5.55/1.09    inference(avatar_split_clause,[],[f504,f485,f500,f481])).
% 5.55/1.09  fof(f485,plain,(
% 5.55/1.09    spl6_9 <=> ! [X0] : (~r2_hidden(sK4(sK0,sK1),X0) | ~r1_xboole_0(k1_tarski(sK3),X0))),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 5.55/1.09  fof(f504,plain,(
% 5.55/1.09    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) | r1_xboole_0(sK0,sK1) | ~spl6_9),
% 5.55/1.09    inference(forward_demodulation,[],[f494,f61])).
% 5.55/1.09  fof(f494,plain,(
% 5.55/1.09    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK0)) | r1_xboole_0(sK0,sK1) | ~spl6_9),
% 5.55/1.09    inference(resolution,[],[f486,f143])).
% 5.55/1.09  fof(f143,plain,(
% 5.55/1.09    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 5.55/1.09    inference(superposition,[],[f50,f61])).
% 5.55/1.09  fof(f50,plain,(
% 5.55/1.09    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f30])).
% 5.55/1.09  fof(f30,plain,(
% 5.55/1.09    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 5.55/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f29])).
% 5.55/1.09  fof(f29,plain,(
% 5.55/1.09    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 5.55/1.09    introduced(choice_axiom,[])).
% 5.55/1.09  fof(f25,plain,(
% 5.55/1.09    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 5.55/1.09    inference(ennf_transformation,[],[f17])).
% 5.55/1.09  fof(f17,plain,(
% 5.55/1.09    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.55/1.09    inference(rectify,[],[f4])).
% 5.55/1.09  fof(f4,axiom,(
% 5.55/1.09    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 5.55/1.09  fof(f486,plain,(
% 5.55/1.09    ( ! [X0] : (~r2_hidden(sK4(sK0,sK1),X0) | ~r1_xboole_0(k1_tarski(sK3),X0)) ) | ~spl6_9),
% 5.55/1.09    inference(avatar_component_clause,[],[f485])).
% 5.55/1.09  fof(f487,plain,(
% 5.55/1.09    spl6_8 | spl6_9 | ~spl6_4),
% 5.55/1.09    inference(avatar_split_clause,[],[f474,f83,f485,f481])).
% 5.55/1.09  fof(f83,plain,(
% 5.55/1.09    spl6_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 5.55/1.09  fof(f474,plain,(
% 5.55/1.09    ( ! [X0] : (~r2_hidden(sK4(sK0,sK1),X0) | ~r1_xboole_0(k1_tarski(sK3),X0) | r1_xboole_0(sK0,sK1)) ) | ~spl6_4),
% 5.55/1.09    inference(resolution,[],[f290,f50])).
% 5.55/1.09  fof(f290,plain,(
% 5.55/1.09    ( ! [X0,X1] : (~r2_hidden(X1,k3_xboole_0(sK0,sK1)) | ~r2_hidden(X1,X0) | ~r1_xboole_0(k1_tarski(sK3),X0)) ) | ~spl6_4),
% 5.55/1.09    inference(resolution,[],[f211,f124])).
% 5.55/1.09  fof(f124,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 5.55/1.09    inference(superposition,[],[f65,f46])).
% 5.55/1.09  fof(f46,plain,(
% 5.55/1.09    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f28])).
% 5.55/1.09  fof(f28,plain,(
% 5.55/1.09    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 5.55/1.09    inference(nnf_transformation,[],[f10])).
% 5.55/1.09  fof(f10,axiom,(
% 5.55/1.09    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 5.55/1.09  fof(f65,plain,(
% 5.55/1.09    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 5.55/1.09    inference(equality_resolution,[],[f54])).
% 5.55/1.09  fof(f54,plain,(
% 5.55/1.09    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 5.55/1.09    inference(cnf_transformation,[],[f35])).
% 5.55/1.09  fof(f35,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.55/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 5.55/1.09  fof(f34,plain,(
% 5.55/1.09    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 5.55/1.09    introduced(choice_axiom,[])).
% 5.55/1.09  fof(f33,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.55/1.09    inference(rectify,[],[f32])).
% 5.55/1.09  fof(f32,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.55/1.09    inference(flattening,[],[f31])).
% 5.55/1.09  fof(f31,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 5.55/1.09    inference(nnf_transformation,[],[f2])).
% 5.55/1.09  fof(f2,axiom,(
% 5.55/1.09    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 5.55/1.09  fof(f211,plain,(
% 5.55/1.09    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X0) | ~r1_xboole_0(k1_tarski(sK3),X0)) ) | ~spl6_4),
% 5.55/1.09    inference(resolution,[],[f112,f85])).
% 5.55/1.09  fof(f85,plain,(
% 5.55/1.09    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl6_4),
% 5.55/1.09    inference(avatar_component_clause,[],[f83])).
% 5.55/1.09  fof(f112,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 5.55/1.09    inference(superposition,[],[f45,f46])).
% 5.55/1.09  fof(f45,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f22])).
% 5.55/1.09  fof(f22,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 5.55/1.09    inference(ennf_transformation,[],[f5])).
% 5.55/1.09  fof(f5,axiom,(
% 5.55/1.09    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 5.55/1.09  fof(f353,plain,(
% 5.55/1.09    ~spl6_7 | spl6_1 | ~spl6_5),
% 5.55/1.09    inference(avatar_split_clause,[],[f348,f90,f68,f350])).
% 5.55/1.09  fof(f68,plain,(
% 5.55/1.09    spl6_1 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 5.55/1.09  fof(f90,plain,(
% 5.55/1.09    spl6_5 <=> r1_xboole_0(sK1,sK2)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 5.55/1.09  fof(f348,plain,(
% 5.55/1.09    ~r1_xboole_0(sK1,sK0) | (spl6_1 | ~spl6_5)),
% 5.55/1.09    inference(subsumption_resolution,[],[f342,f92])).
% 5.55/1.09  fof(f92,plain,(
% 5.55/1.09    r1_xboole_0(sK1,sK2) | ~spl6_5),
% 5.55/1.09    inference(avatar_component_clause,[],[f90])).
% 5.55/1.09  fof(f342,plain,(
% 5.55/1.09    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl6_1),
% 5.55/1.09    inference(resolution,[],[f152,f70])).
% 5.55/1.09  fof(f70,plain,(
% 5.55/1.09    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl6_1),
% 5.55/1.09    inference(avatar_component_clause,[],[f68])).
% 5.55/1.09  fof(f152,plain,(
% 5.55/1.09    ( ! [X6,X8,X7] : (r1_xboole_0(k2_xboole_0(X7,X8),X6) | ~r1_xboole_0(X6,X8) | ~r1_xboole_0(X6,X7)) )),
% 5.55/1.09    inference(resolution,[],[f40,f48])).
% 5.55/1.09  fof(f40,plain,(
% 5.55/1.09    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 5.55/1.09    inference(cnf_transformation,[],[f20])).
% 5.55/1.09  fof(f20,plain,(
% 5.55/1.09    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 5.55/1.09    inference(ennf_transformation,[],[f7])).
% 5.55/1.09  fof(f7,axiom,(
% 5.55/1.09    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 5.55/1.09  fof(f237,plain,(
% 5.55/1.09    ~spl6_6 | ~spl6_3 | ~spl6_5),
% 5.55/1.09    inference(avatar_split_clause,[],[f231,f90,f78,f234])).
% 5.55/1.09  fof(f78,plain,(
% 5.55/1.09    spl6_3 <=> r2_hidden(sK3,sK2)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 5.55/1.09  fof(f231,plain,(
% 5.55/1.09    ~r2_hidden(sK3,sK1) | (~spl6_3 | ~spl6_5)),
% 5.55/1.09    inference(resolution,[],[f229,f80])).
% 5.55/1.09  fof(f80,plain,(
% 5.55/1.09    r2_hidden(sK3,sK2) | ~spl6_3),
% 5.55/1.09    inference(avatar_component_clause,[],[f78])).
% 5.55/1.09  fof(f229,plain,(
% 5.55/1.09    ( ! [X60] : (~r2_hidden(X60,sK2) | ~r2_hidden(X60,sK1)) ) | ~spl6_5),
% 5.55/1.09    inference(resolution,[],[f124,f92])).
% 5.55/1.09  fof(f93,plain,(
% 5.55/1.09    spl6_5 | ~spl6_2),
% 5.55/1.09    inference(avatar_split_clause,[],[f87,f73,f90])).
% 5.55/1.09  fof(f73,plain,(
% 5.55/1.09    spl6_2 <=> r1_xboole_0(sK2,sK1)),
% 5.55/1.09    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 5.55/1.09  fof(f87,plain,(
% 5.55/1.09    r1_xboole_0(sK1,sK2) | ~spl6_2),
% 5.55/1.09    inference(resolution,[],[f48,f75])).
% 5.55/1.09  fof(f75,plain,(
% 5.55/1.09    r1_xboole_0(sK2,sK1) | ~spl6_2),
% 5.55/1.09    inference(avatar_component_clause,[],[f73])).
% 5.55/1.09  fof(f86,plain,(
% 5.55/1.09    spl6_4),
% 5.55/1.09    inference(avatar_split_clause,[],[f36,f83])).
% 5.55/1.09  fof(f36,plain,(
% 5.55/1.09    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 5.55/1.09    inference(cnf_transformation,[],[f27])).
% 5.55/1.09  fof(f27,plain,(
% 5.55/1.09    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 5.55/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f26])).
% 5.55/1.09  fof(f26,plain,(
% 5.55/1.09    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 5.55/1.09    introduced(choice_axiom,[])).
% 5.55/1.09  fof(f19,plain,(
% 5.55/1.09    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 5.55/1.09    inference(flattening,[],[f18])).
% 5.55/1.09  fof(f18,plain,(
% 5.55/1.09    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 5.55/1.09    inference(ennf_transformation,[],[f16])).
% 5.55/1.09  fof(f16,negated_conjecture,(
% 5.55/1.09    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 5.55/1.09    inference(negated_conjecture,[],[f15])).
% 5.55/1.09  fof(f15,conjecture,(
% 5.55/1.09    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 5.55/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 5.55/1.09  fof(f81,plain,(
% 5.55/1.09    spl6_3),
% 5.55/1.09    inference(avatar_split_clause,[],[f37,f78])).
% 5.55/1.09  fof(f37,plain,(
% 5.55/1.09    r2_hidden(sK3,sK2)),
% 5.55/1.09    inference(cnf_transformation,[],[f27])).
% 5.55/1.09  fof(f76,plain,(
% 5.55/1.09    spl6_2),
% 5.55/1.09    inference(avatar_split_clause,[],[f38,f73])).
% 5.55/1.09  fof(f38,plain,(
% 5.55/1.09    r1_xboole_0(sK2,sK1)),
% 5.55/1.09    inference(cnf_transformation,[],[f27])).
% 5.55/1.09  fof(f71,plain,(
% 5.55/1.09    ~spl6_1),
% 5.55/1.09    inference(avatar_split_clause,[],[f39,f68])).
% 5.55/1.09  fof(f39,plain,(
% 5.55/1.09    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 5.55/1.09    inference(cnf_transformation,[],[f27])).
% 5.55/1.09  % SZS output end Proof for theBenchmark
% 5.55/1.09  % (22557)------------------------------
% 5.55/1.09  % (22557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.55/1.09  % (22557)Termination reason: Refutation
% 5.55/1.09  
% 5.55/1.09  % (22557)Memory used [KB]: 6524
% 5.55/1.09  % (22557)Time elapsed: 0.152 s
% 5.55/1.09  % (22557)------------------------------
% 5.55/1.09  % (22557)------------------------------
% 5.55/1.10  % (22561)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.55/1.11  % (22500)Success in time 0.775 s
%------------------------------------------------------------------------------
