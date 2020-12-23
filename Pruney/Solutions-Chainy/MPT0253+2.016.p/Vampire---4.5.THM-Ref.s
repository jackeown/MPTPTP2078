%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:08 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 382 expanded)
%              Number of leaves         :   23 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 (1326 expanded)
%              Number of equality atoms :   75 ( 371 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f192,f209,f243,f1349,f1503])).

fof(f1503,plain,
    ( spl5_7
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1502])).

fof(f1502,plain,
    ( $false
    | spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f1501,f208])).

fof(f208,plain,
    ( sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_7
  <=> sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1501,plain,
    ( sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f1500,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1500,plain,
    ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0))
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f1463,f313])).

fof(f313,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f307,f308])).

fof(f308,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f263,f263,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f63,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f263,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f233,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f233,plain,(
    ! [X6,X5] : ~ r2_hidden(X6,k5_xboole_0(X5,X5)) ),
    inference(subsumption_resolution,[],[f229,f228])).

fof(f228,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f94,f105])).

fof(f105,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f90,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f47])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f229,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k5_xboole_0(X5,X5))
      | ~ r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f93,f105])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f47])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f307,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f233,f263,f83])).

fof(f1463,plain,
    ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))))
    | ~ spl5_13 ),
    inference(superposition,[],[f78,f1348])).

fof(f1348,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1346])).

fof(f1346,plain,
    ( spl5_13
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f48,f74,f47,f74])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1349,plain,
    ( spl5_13
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f276,f240,f1346])).

fof(f240,plain,
    ( spl5_9
  <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f276,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f242,f52])).

fof(f242,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f240])).

fof(f243,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f155,f101,f96,f240])).

fof(f96,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f101,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f155,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f98,f103,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f103,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f98,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f209,plain,
    ( ~ spl5_7
    | spl5_6 ),
    inference(avatar_split_clause,[],[f193,f189,f206])).

fof(f189,plain,
    ( spl5_6
  <=> sK1 = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f193,plain,
    ( sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))
    | spl5_6 ),
    inference(forward_demodulation,[],[f191,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f44,f73,f73])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f191,plain,
    ( sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f192,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f75,f189])).

fof(f75,plain,(
    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f41,f74,f73])).

fof(f41,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f104,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26555)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (26543)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (26546)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (26563)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (26553)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (26571)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (26571)Refutation not found, incomplete strategy% (26571)------------------------------
% 0.20/0.52  % (26571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26554)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (26564)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (26542)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26560)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.53  % (26556)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.53  % (26571)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (26571)Memory used [KB]: 1663
% 1.29/0.53  % (26571)Time elapsed: 0.105 s
% 1.29/0.53  % (26571)------------------------------
% 1.29/0.53  % (26571)------------------------------
% 1.29/0.53  % (26544)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.53  % (26545)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.53  % (26547)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.53  % (26562)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.53  % (26550)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.53  % (26569)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.54  % (26548)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (26566)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.54  % (26570)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.54  % (26570)Refutation not found, incomplete strategy% (26570)------------------------------
% 1.29/0.54  % (26570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26570)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26570)Memory used [KB]: 10746
% 1.29/0.54  % (26570)Time elapsed: 0.127 s
% 1.29/0.54  % (26570)------------------------------
% 1.29/0.54  % (26570)------------------------------
% 1.29/0.54  % (26549)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.54  % (26567)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.54  % (26556)Refutation not found, incomplete strategy% (26556)------------------------------
% 1.29/0.54  % (26556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (26556)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (26556)Memory used [KB]: 1663
% 1.29/0.54  % (26556)Time elapsed: 0.089 s
% 1.29/0.54  % (26556)------------------------------
% 1.29/0.54  % (26556)------------------------------
% 1.29/0.54  % (26561)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.54  % (26568)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (26558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.54  % (26565)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.29/0.55  % (26558)Refutation not found, incomplete strategy% (26558)------------------------------
% 1.29/0.55  % (26558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (26558)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (26558)Memory used [KB]: 10618
% 1.29/0.55  % (26558)Time elapsed: 0.139 s
% 1.29/0.55  % (26558)------------------------------
% 1.29/0.55  % (26558)------------------------------
% 1.29/0.55  % (26559)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.55  % (26559)Refutation not found, incomplete strategy% (26559)------------------------------
% 1.29/0.55  % (26559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (26559)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (26559)Memory used [KB]: 1663
% 1.29/0.55  % (26559)Time elapsed: 0.139 s
% 1.29/0.55  % (26559)------------------------------
% 1.29/0.55  % (26559)------------------------------
% 1.29/0.55  % (26551)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.55  % (26552)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.51/0.55  % (26557)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.55  % (26552)Refutation not found, incomplete strategy% (26552)------------------------------
% 1.51/0.55  % (26552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (26552)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (26552)Memory used [KB]: 10746
% 1.51/0.55  % (26552)Time elapsed: 0.139 s
% 1.51/0.55  % (26552)------------------------------
% 1.51/0.55  % (26552)------------------------------
% 2.06/0.65  % (26545)Refutation not found, incomplete strategy% (26545)------------------------------
% 2.06/0.65  % (26545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.65  % (26545)Termination reason: Refutation not found, incomplete strategy
% 2.06/0.65  
% 2.06/0.65  % (26545)Memory used [KB]: 6140
% 2.06/0.65  % (26545)Time elapsed: 0.236 s
% 2.06/0.65  % (26545)------------------------------
% 2.06/0.65  % (26545)------------------------------
% 2.06/0.67  % (26562)Refutation found. Thanks to Tanya!
% 2.06/0.67  % SZS status Theorem for theBenchmark
% 2.06/0.67  % SZS output start Proof for theBenchmark
% 2.06/0.67  fof(f1548,plain,(
% 2.06/0.67    $false),
% 2.06/0.67    inference(avatar_sat_refutation,[],[f99,f104,f192,f209,f243,f1349,f1503])).
% 2.06/0.67  fof(f1503,plain,(
% 2.06/0.67    spl5_7 | ~spl5_13),
% 2.06/0.67    inference(avatar_contradiction_clause,[],[f1502])).
% 2.06/0.67  fof(f1502,plain,(
% 2.06/0.67    $false | (spl5_7 | ~spl5_13)),
% 2.06/0.67    inference(subsumption_resolution,[],[f1501,f208])).
% 2.06/0.67  fof(f208,plain,(
% 2.06/0.67    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) | spl5_7),
% 2.06/0.67    inference(avatar_component_clause,[],[f206])).
% 2.06/0.67  fof(f206,plain,(
% 2.06/0.67    spl5_7 <=> sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.06/0.67  fof(f1501,plain,(
% 2.06/0.67    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl5_13),
% 2.06/0.67    inference(forward_demodulation,[],[f1500,f76])).
% 2.06/0.67  fof(f76,plain,(
% 2.06/0.67    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 2.06/0.67    inference(definition_unfolding,[],[f42,f74])).
% 2.06/0.67  fof(f74,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.06/0.67    inference(definition_unfolding,[],[f45,f73])).
% 2.06/0.67  fof(f73,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.06/0.67    inference(definition_unfolding,[],[f46,f72])).
% 2.06/0.67  fof(f72,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.06/0.67    inference(definition_unfolding,[],[f58,f71])).
% 2.06/0.67  fof(f71,plain,(
% 2.06/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.06/0.67    inference(definition_unfolding,[],[f69,f70])).
% 2.06/0.67  fof(f70,plain,(
% 2.06/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f15])).
% 2.06/0.67  fof(f15,axiom,(
% 2.06/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.06/0.67  fof(f69,plain,(
% 2.06/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f14])).
% 2.06/0.67  fof(f14,axiom,(
% 2.06/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.06/0.67  fof(f58,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f13])).
% 2.06/0.67  fof(f13,axiom,(
% 2.06/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.06/0.67  fof(f46,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f12])).
% 2.06/0.67  fof(f12,axiom,(
% 2.06/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.06/0.67  fof(f45,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.06/0.67    inference(cnf_transformation,[],[f16])).
% 2.06/0.67  fof(f16,axiom,(
% 2.06/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.06/0.67  fof(f42,plain,(
% 2.06/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.67    inference(cnf_transformation,[],[f5])).
% 2.06/0.67  fof(f5,axiom,(
% 2.06/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.06/0.67  fof(f1500,plain,(
% 2.06/0.67    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) | ~spl5_13),
% 2.06/0.67    inference(forward_demodulation,[],[f1463,f313])).
% 2.06/0.67  fof(f313,plain,(
% 2.06/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.06/0.67    inference(forward_demodulation,[],[f307,f308])).
% 2.06/0.67  fof(f308,plain,(
% 2.06/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 2.06/0.67    inference(unit_resulting_resolution,[],[f263,f263,f83])).
% 2.06/0.67  fof(f83,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.06/0.67    inference(definition_unfolding,[],[f63,f47])).
% 2.06/0.67  fof(f47,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.06/0.67    inference(cnf_transformation,[],[f4])).
% 2.06/0.67  fof(f4,axiom,(
% 2.06/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.06/0.67  fof(f63,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f36])).
% 2.06/0.67  fof(f36,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.06/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 2.06/0.67  fof(f35,plain,(
% 2.06/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.06/0.67    introduced(choice_axiom,[])).
% 2.06/0.67  fof(f34,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.06/0.67    inference(rectify,[],[f33])).
% 2.06/0.67  fof(f33,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.06/0.67    inference(flattening,[],[f32])).
% 2.06/0.67  fof(f32,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.06/0.67    inference(nnf_transformation,[],[f1])).
% 2.06/0.67  fof(f1,axiom,(
% 2.06/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.06/0.67  fof(f263,plain,(
% 2.06/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.06/0.67    inference(superposition,[],[f233,f43])).
% 2.06/0.67  fof(f43,plain,(
% 2.06/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.67    inference(cnf_transformation,[],[f8])).
% 2.06/0.67  fof(f8,axiom,(
% 2.06/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.06/0.67  fof(f233,plain,(
% 2.06/0.67    ( ! [X6,X5] : (~r2_hidden(X6,k5_xboole_0(X5,X5))) )),
% 2.06/0.67    inference(subsumption_resolution,[],[f229,f228])).
% 2.06/0.67  fof(f228,plain,(
% 2.06/0.67    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | r2_hidden(X4,X3)) )),
% 2.06/0.67    inference(superposition,[],[f94,f105])).
% 2.06/0.67  fof(f105,plain,(
% 2.06/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.06/0.67    inference(unit_resulting_resolution,[],[f90,f52])).
% 2.06/0.67  fof(f52,plain,(
% 2.06/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.06/0.67    inference(cnf_transformation,[],[f24])).
% 2.06/0.67  fof(f24,plain,(
% 2.06/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.06/0.67    inference(ennf_transformation,[],[f6])).
% 2.06/0.67  fof(f6,axiom,(
% 2.06/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.06/0.67  fof(f90,plain,(
% 2.06/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.67    inference(equality_resolution,[],[f54])).
% 2.06/0.67  fof(f54,plain,(
% 2.06/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.67    inference(cnf_transformation,[],[f30])).
% 2.06/0.67  fof(f30,plain,(
% 2.06/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.67    inference(flattening,[],[f29])).
% 2.06/0.67  fof(f29,plain,(
% 2.06/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.67    inference(nnf_transformation,[],[f3])).
% 2.06/0.67  fof(f3,axiom,(
% 2.06/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.67  fof(f94,plain,(
% 2.06/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 2.06/0.67    inference(equality_resolution,[],[f86])).
% 2.06/0.67  fof(f86,plain,(
% 2.06/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.06/0.67    inference(definition_unfolding,[],[f60,f47])).
% 2.06/0.67  fof(f60,plain,(
% 2.06/0.67    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.06/0.67    inference(cnf_transformation,[],[f36])).
% 2.06/0.67  fof(f229,plain,(
% 2.06/0.67    ( ! [X6,X5] : (~r2_hidden(X6,k5_xboole_0(X5,X5)) | ~r2_hidden(X6,X5)) )),
% 2.06/0.67    inference(superposition,[],[f93,f105])).
% 2.06/0.67  fof(f93,plain,(
% 2.06/0.67    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.06/0.67    inference(equality_resolution,[],[f85])).
% 2.06/0.67  fof(f85,plain,(
% 2.06/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.06/0.67    inference(definition_unfolding,[],[f61,f47])).
% 2.06/0.67  fof(f61,plain,(
% 2.06/0.67    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.06/0.67    inference(cnf_transformation,[],[f36])).
% 2.06/0.67  fof(f307,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) )),
% 2.06/0.67    inference(unit_resulting_resolution,[],[f233,f263,f83])).
% 2.06/0.67  fof(f1463,plain,(
% 2.06/0.67    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2)))) | ~spl5_13),
% 2.06/0.67    inference(superposition,[],[f78,f1348])).
% 2.06/0.67  fof(f1348,plain,(
% 2.06/0.67    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_13),
% 2.06/0.67    inference(avatar_component_clause,[],[f1346])).
% 2.06/0.67  fof(f1346,plain,(
% 2.06/0.67    spl5_13 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.06/0.67  fof(f78,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.06/0.67    inference(definition_unfolding,[],[f48,f74,f47,f74])).
% 2.06/0.67  fof(f48,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f7])).
% 2.06/0.67  fof(f7,axiom,(
% 2.06/0.67    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.06/0.67  fof(f1349,plain,(
% 2.06/0.67    spl5_13 | ~spl5_9),
% 2.06/0.67    inference(avatar_split_clause,[],[f276,f240,f1346])).
% 2.06/0.67  fof(f240,plain,(
% 2.06/0.67    spl5_9 <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.06/0.67  fof(f276,plain,(
% 2.06/0.67    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_9),
% 2.06/0.67    inference(unit_resulting_resolution,[],[f242,f52])).
% 2.06/0.67  fof(f242,plain,(
% 2.06/0.67    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_9),
% 2.06/0.67    inference(avatar_component_clause,[],[f240])).
% 2.06/0.67  fof(f243,plain,(
% 2.06/0.67    spl5_9 | ~spl5_1 | ~spl5_2),
% 2.06/0.67    inference(avatar_split_clause,[],[f155,f101,f96,f240])).
% 2.06/0.67  fof(f96,plain,(
% 2.06/0.67    spl5_1 <=> r2_hidden(sK0,sK1)),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.06/0.67  fof(f101,plain,(
% 2.06/0.67    spl5_2 <=> r2_hidden(sK2,sK1)),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.06/0.67  fof(f155,plain,(
% 2.06/0.67    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1) | (~spl5_1 | ~spl5_2)),
% 2.06/0.67    inference(unit_resulting_resolution,[],[f98,f103,f87])).
% 2.06/0.67  fof(f87,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.06/0.67    inference(definition_unfolding,[],[f68,f73])).
% 2.06/0.67  fof(f68,plain,(
% 2.06/0.67    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f38])).
% 2.06/0.67  fof(f38,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.06/0.67    inference(flattening,[],[f37])).
% 2.06/0.67  fof(f37,plain,(
% 2.06/0.67    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.06/0.67    inference(nnf_transformation,[],[f17])).
% 2.06/0.67  fof(f17,axiom,(
% 2.06/0.67    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.06/0.67  fof(f103,plain,(
% 2.06/0.67    r2_hidden(sK2,sK1) | ~spl5_2),
% 2.06/0.67    inference(avatar_component_clause,[],[f101])).
% 2.06/0.67  fof(f98,plain,(
% 2.06/0.67    r2_hidden(sK0,sK1) | ~spl5_1),
% 2.06/0.67    inference(avatar_component_clause,[],[f96])).
% 2.06/0.67  fof(f209,plain,(
% 2.06/0.67    ~spl5_7 | spl5_6),
% 2.06/0.67    inference(avatar_split_clause,[],[f193,f189,f206])).
% 2.06/0.67  fof(f189,plain,(
% 2.06/0.67    spl5_6 <=> sK1 = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 2.06/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.06/0.67  fof(f193,plain,(
% 2.06/0.67    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2))) | spl5_6),
% 2.06/0.67    inference(forward_demodulation,[],[f191,f77])).
% 2.06/0.67  fof(f77,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 2.06/0.67    inference(definition_unfolding,[],[f44,f73,f73])).
% 2.06/0.67  fof(f44,plain,(
% 2.06/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.06/0.67    inference(cnf_transformation,[],[f11])).
% 2.06/0.67  fof(f11,axiom,(
% 2.06/0.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.06/0.67  fof(f191,plain,(
% 2.06/0.67    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1)) | spl5_6),
% 2.06/0.67    inference(avatar_component_clause,[],[f189])).
% 2.06/0.67  fof(f192,plain,(
% 2.06/0.67    ~spl5_6),
% 2.06/0.67    inference(avatar_split_clause,[],[f75,f189])).
% 2.06/0.67  fof(f75,plain,(
% 2.06/0.67    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),sK1))),
% 2.06/0.67    inference(definition_unfolding,[],[f41,f74,f73])).
% 2.06/0.67  fof(f41,plain,(
% 2.06/0.67    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 2.06/0.67    inference(cnf_transformation,[],[f26])).
% 2.06/0.67  fof(f26,plain,(
% 2.06/0.67    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 2.06/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).
% 2.06/0.67  fof(f25,plain,(
% 2.06/0.67    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 2.06/0.67    introduced(choice_axiom,[])).
% 2.06/0.67  fof(f22,plain,(
% 2.06/0.67    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 2.06/0.67    inference(flattening,[],[f21])).
% 2.06/0.67  fof(f21,plain,(
% 2.06/0.67    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 2.06/0.67    inference(ennf_transformation,[],[f19])).
% 2.06/0.67  fof(f19,negated_conjecture,(
% 2.06/0.67    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 2.06/0.67    inference(negated_conjecture,[],[f18])).
% 2.06/0.67  fof(f18,conjecture,(
% 2.06/0.67    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 2.06/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 2.06/0.67  fof(f104,plain,(
% 2.06/0.67    spl5_2),
% 2.06/0.67    inference(avatar_split_clause,[],[f40,f101])).
% 2.06/0.67  fof(f40,plain,(
% 2.06/0.67    r2_hidden(sK2,sK1)),
% 2.06/0.67    inference(cnf_transformation,[],[f26])).
% 2.06/0.67  fof(f99,plain,(
% 2.06/0.67    spl5_1),
% 2.06/0.67    inference(avatar_split_clause,[],[f39,f96])).
% 2.06/0.67  fof(f39,plain,(
% 2.06/0.67    r2_hidden(sK0,sK1)),
% 2.06/0.67    inference(cnf_transformation,[],[f26])).
% 2.06/0.67  % SZS output end Proof for theBenchmark
% 2.06/0.67  % (26562)------------------------------
% 2.06/0.67  % (26562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.67  % (26562)Termination reason: Refutation
% 2.06/0.67  
% 2.06/0.67  % (26562)Memory used [KB]: 12153
% 2.06/0.67  % (26562)Time elapsed: 0.218 s
% 2.06/0.67  % (26562)------------------------------
% 2.06/0.67  % (26562)------------------------------
% 2.06/0.67  % (26572)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.06/0.67  % (26574)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.34/0.68  % (26577)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.34/0.68  % (26576)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.34/0.69  % (26576)Refutation not found, incomplete strategy% (26576)------------------------------
% 2.34/0.69  % (26576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.34/0.69  % (26576)Termination reason: Refutation not found, incomplete strategy
% 2.34/0.69  
% 2.34/0.69  % (26576)Memory used [KB]: 10618
% 2.34/0.69  % (26576)Time elapsed: 0.107 s
% 2.34/0.69  % (26576)------------------------------
% 2.34/0.69  % (26576)------------------------------
% 2.34/0.69  % (26573)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.34/0.69  % (26541)Success in time 0.327 s
%------------------------------------------------------------------------------
