%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:27 EST 2020

% Result     : Theorem 3.79s
% Output     : Refutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 467 expanded)
%              Number of leaves         :   19 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  538 (2769 expanded)
%              Number of equality atoms :  149 ( 698 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f81,f82,f156,f193,f870,f920,f1047,f1765,f2624,f3434,f3483,f3533])).

fof(f3533,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_55 ),
    inference(avatar_contradiction_clause,[],[f3532])).

fof(f3532,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f3502,f2459])).

fof(f2459,plain,
    ( k1_tarski(sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f2451,f936])).

fof(f936,plain,
    ( ! [X6] : ~ r2_hidden(sK1,k4_xboole_0(X6,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f78,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f2451,plain,
    ( ! [X2] :
        ( k1_tarski(sK1) = k2_tarski(sK1,sK1)
        | r2_hidden(sK1,k4_xboole_0(X2,sK2)) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f2434])).

fof(f2434,plain,
    ( ! [X2] :
        ( k1_tarski(sK1) = k2_tarski(sK1,sK1)
        | r2_hidden(sK1,k4_xboole_0(X2,sK2))
        | r2_hidden(sK1,k4_xboole_0(X2,sK2)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f998,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f998,plain,
    ( ! [X16] : k1_tarski(sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(X16,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f936,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f3502,plain,
    ( k1_tarski(sK1) != k2_tarski(sK1,sK1)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_55 ),
    inference(backward_demodulation,[],[f2284,f3433])).

fof(f3433,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f3431])).

fof(f3431,plain,
    ( spl5_55
  <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f2284,plain,
    ( k1_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)) != k2_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK1)
    | spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f1340,f1737])).

fof(f1737,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1736,f1141])).

fof(f1141,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f59,f931])).

fof(f931,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f1736,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2)
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f1079])).

fof(f1079,plain,
    ( ! [X1] :
        ( k1_xboole_0 != X1
        | ~ r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),sK2)
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),X1) )
    | spl5_1 ),
    inference(superposition,[],[f71,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1340,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k1_tarski(X0) != k2_tarski(X0,sK1) )
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1331,f78])).

fof(f1331,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k2_tarski(X0,sK1)
        | ~ r2_hidden(sK1,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f930,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f930,plain,
    ( ! [X1] : k2_tarski(X1,sK1) != k4_xboole_0(k2_tarski(X1,sK1),sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3483,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_54 ),
    inference(avatar_contradiction_clause,[],[f3482])).

fof(f3482,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f3453,f2727])).

fof(f2727,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f2719,f1057])).

fof(f1057,plain,
    ( ! [X6] : ~ r2_hidden(sK0,k4_xboole_0(X6,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2719,plain,
    ( ! [X2] :
        ( k1_tarski(sK0) = k2_tarski(sK0,sK0)
        | r2_hidden(sK0,k4_xboole_0(X2,sK2)) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f2702])).

fof(f2702,plain,
    ( ! [X2] :
        ( k1_tarski(sK0) = k2_tarski(sK0,sK0)
        | r2_hidden(sK0,k4_xboole_0(X2,sK2))
        | r2_hidden(sK0,k4_xboole_0(X2,sK2)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f1112,f42])).

fof(f1112,plain,
    ( ! [X16] : k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(X16,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f1057,f66])).

fof(f3453,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_54 ),
    inference(backward_demodulation,[],[f2327,f3429])).

fof(f3429,plain,
    ( sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f3427])).

fof(f3427,plain,
    ( spl5_54
  <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f2327,plain,
    ( k1_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)) != k2_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f1478,f1737])).

fof(f1478,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | k1_tarski(X0) != k2_tarski(X0,sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1469,f74])).

fof(f1469,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k2_tarski(X0,sK0)
        | ~ r2_hidden(sK0,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f1051,f53])).

fof(f1051,plain,
    ( ! [X1] : k2_tarski(X1,sK0) != k4_xboole_0(k2_tarski(X1,sK0),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f41])).

fof(f3434,plain,
    ( spl5_54
    | spl5_55
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f3414,f1762,f3431,f3427])).

fof(f1762,plain,
    ( spl5_26
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f3414,plain,
    ( sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_26 ),
    inference(resolution,[],[f1764,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f1764,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f2624,plain,
    ( ~ spl5_3
    | spl5_8
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f2622])).

fof(f2622,plain,
    ( $false
    | ~ spl5_3
    | spl5_8
    | ~ spl5_25 ),
    inference(resolution,[],[f2580,f1760])).

fof(f1760,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1758,plain,
    ( spl5_25
  <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f2580,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl5_3
    | spl5_8 ),
    inference(subsumption_resolution,[],[f2575,f1140])).

fof(f1140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,k1_tarski(sK1)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f60,f931])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2575,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK1))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl5_3
    | spl5_8 ),
    inference(superposition,[],[f59,f2460])).

fof(f2460,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | ~ spl5_3
    | spl5_8 ),
    inference(backward_demodulation,[],[f962,f2459])).

fof(f962,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)
    | spl5_8 ),
    inference(resolution,[],[f192,f66])).

fof(f192,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_8
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1765,plain,
    ( spl5_25
    | spl5_26
    | spl5_1 ),
    inference(avatar_split_clause,[],[f1756,f69,f1762,f1758])).

fof(f1756,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))
    | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f1078])).

fof(f1078,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1))
        | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f71,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1047,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl5_6 ),
    inference(resolution,[],[f1031,f125])).

fof(f125,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_6
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1031,plain,
    ( ! [X11] : ~ r2_hidden(X11,k1_xboole_0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1023,f125])).

fof(f1023,plain,
    ( ! [X11] :
        ( ~ r2_hidden(sK0,k1_xboole_0)
        | ~ r2_hidden(X11,k1_xboole_0) )
    | ~ spl5_6 ),
    inference(superposition,[],[f946,f50])).

fof(f946,plain,
    ( ! [X6] : ~ r2_hidden(sK0,k4_xboole_0(X6,k1_xboole_0))
    | ~ spl5_6 ),
    inference(resolution,[],[f125,f59])).

fof(f920,plain,
    ( ~ spl5_1
    | spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f918,f64])).

fof(f64,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f918,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_1
    | spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f908,f126])).

fof(f126,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f908,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f75,f220])).

fof(f220,plain,
    ( ! [X2] :
        ( r2_hidden(X2,sK2)
        | r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k2_tarski(sK0,sK1)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f58,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f870,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f864])).

fof(f864,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f821,f702])).

fof(f702,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_1
    | spl5_3 ),
    inference(superposition,[],[f410,f70])).

fof(f410,plain,
    ( ! [X20] : r2_hidden(sK1,k4_xboole_0(k2_tarski(X20,sK1),sK2))
    | spl5_3 ),
    inference(resolution,[],[f200,f62])).

fof(f62,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f200,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK1,X5)
        | r2_hidden(sK1,k4_xboole_0(X5,sK2)) )
    | spl5_3 ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f821,plain,
    ( ! [X11] : ~ r2_hidden(X11,k1_xboole_0)
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f812,f702])).

fof(f812,plain,
    ( ! [X11] :
        ( ~ r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X11,k1_xboole_0) )
    | ~ spl5_1
    | spl5_3 ),
    inference(superposition,[],[f737,f50])).

fof(f737,plain,
    ( ! [X6] : ~ r2_hidden(sK1,k4_xboole_0(X6,k1_xboole_0))
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f702,f59])).

fof(f193,plain,
    ( spl5_4
    | ~ spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f184,f77,f190,f117])).

fof(f117,plain,
    ( spl5_4
  <=> ! [X7] : ~ r2_hidden(X7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f184,plain,
    ( ! [X11] :
        ( ~ r2_hidden(sK1,k1_xboole_0)
        | ~ r2_hidden(X11,sK2) )
    | ~ spl5_3 ),
    inference(superposition,[],[f98,f50])).

fof(f98,plain,
    ( ! [X6] : ~ r2_hidden(sK1,k4_xboole_0(X6,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f59])).

fof(f156,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f118,f74])).

fof(f118,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f82,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f31,f73,f69])).

fof(f31,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f81,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f32,f77,f69])).

fof(f32,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f77,f73,f69])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (12896)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.45  % (12903)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.49  % (12914)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.49  % (12894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (12912)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.49  % (12900)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (12892)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (12911)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (12893)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (12905)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12904)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12909)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (12890)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (12897)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (12897)Refutation not found, incomplete strategy% (12897)------------------------------
% 0.22/0.51  % (12897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12897)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12897)Memory used [KB]: 10618
% 0.22/0.51  % (12897)Time elapsed: 0.105 s
% 0.22/0.51  % (12897)------------------------------
% 0.22/0.51  % (12897)------------------------------
% 0.22/0.51  % (12899)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (12901)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.52  % (12898)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.30/0.52  % (12906)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.30/0.52  % (12916)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.30/0.53  % (12902)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.30/0.53  % (12910)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.30/0.53  % (12908)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.53  % (12917)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.30/0.54  % (12891)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (12915)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.55  % (12907)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.10/0.65  % (12900)Refutation not found, incomplete strategy% (12900)------------------------------
% 2.10/0.65  % (12900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (12900)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.65  
% 2.10/0.65  % (12900)Memory used [KB]: 6140
% 2.10/0.65  % (12900)Time elapsed: 0.237 s
% 2.10/0.65  % (12900)------------------------------
% 2.10/0.65  % (12900)------------------------------
% 3.79/0.86  % (12902)Refutation found. Thanks to Tanya!
% 3.79/0.86  % SZS status Theorem for theBenchmark
% 3.79/0.87  % SZS output start Proof for theBenchmark
% 3.79/0.87  fof(f3538,plain,(
% 3.79/0.87    $false),
% 3.79/0.87    inference(avatar_sat_refutation,[],[f80,f81,f82,f156,f193,f870,f920,f1047,f1765,f2624,f3434,f3483,f3533])).
% 3.79/0.87  fof(f3533,plain,(
% 3.79/0.87    spl5_1 | ~spl5_3 | ~spl5_55),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f3532])).
% 3.79/0.87  fof(f3532,plain,(
% 3.79/0.87    $false | (spl5_1 | ~spl5_3 | ~spl5_55)),
% 3.79/0.87    inference(subsumption_resolution,[],[f3502,f2459])).
% 3.79/0.87  fof(f2459,plain,(
% 3.79/0.87    k1_tarski(sK1) = k2_tarski(sK1,sK1) | ~spl5_3),
% 3.79/0.87    inference(subsumption_resolution,[],[f2451,f936])).
% 3.79/0.87  fof(f936,plain,(
% 3.79/0.87    ( ! [X6] : (~r2_hidden(sK1,k4_xboole_0(X6,sK2))) ) | ~spl5_3),
% 3.79/0.87    inference(resolution,[],[f78,f59])).
% 3.79/0.87  fof(f59,plain,(
% 3.79/0.87    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.79/0.87    inference(equality_resolution,[],[f35])).
% 3.79/0.87  fof(f35,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f18])).
% 3.79/0.87  fof(f18,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.79/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 3.79/0.87  fof(f17,plain,(
% 3.79/0.87    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.79/0.87    introduced(choice_axiom,[])).
% 3.79/0.87  fof(f16,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.79/0.87    inference(rectify,[],[f15])).
% 3.79/0.87  fof(f15,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.79/0.87    inference(flattening,[],[f14])).
% 3.79/0.87  fof(f14,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.79/0.87    inference(nnf_transformation,[],[f1])).
% 3.79/0.87  fof(f1,axiom,(
% 3.79/0.87    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.79/0.87  fof(f78,plain,(
% 3.79/0.87    r2_hidden(sK1,sK2) | ~spl5_3),
% 3.79/0.87    inference(avatar_component_clause,[],[f77])).
% 3.79/0.87  fof(f77,plain,(
% 3.79/0.87    spl5_3 <=> r2_hidden(sK1,sK2)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.79/0.87  fof(f2451,plain,(
% 3.79/0.87    ( ! [X2] : (k1_tarski(sK1) = k2_tarski(sK1,sK1) | r2_hidden(sK1,k4_xboole_0(X2,sK2))) ) | ~spl5_3),
% 3.79/0.87    inference(duplicate_literal_removal,[],[f2434])).
% 3.79/0.87  fof(f2434,plain,(
% 3.79/0.87    ( ! [X2] : (k1_tarski(sK1) = k2_tarski(sK1,sK1) | r2_hidden(sK1,k4_xboole_0(X2,sK2)) | r2_hidden(sK1,k4_xboole_0(X2,sK2))) ) | ~spl5_3),
% 3.79/0.87    inference(superposition,[],[f998,f42])).
% 3.79/0.87  fof(f42,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f20])).
% 3.79/0.87  fof(f20,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(flattening,[],[f19])).
% 3.79/0.87  fof(f19,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(nnf_transformation,[],[f6])).
% 3.79/0.87  fof(f6,axiom,(
% 3.79/0.87    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 3.79/0.87  fof(f998,plain,(
% 3.79/0.87    ( ! [X16] : (k1_tarski(sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(X16,sK2))) ) | ~spl5_3),
% 3.79/0.87    inference(resolution,[],[f936,f66])).
% 3.79/0.87  fof(f66,plain,(
% 3.79/0.87    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 3.79/0.87    inference(equality_resolution,[],[f54])).
% 3.79/0.87  fof(f54,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f28])).
% 3.79/0.87  fof(f28,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(flattening,[],[f27])).
% 3.79/0.87  fof(f27,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(nnf_transformation,[],[f4])).
% 3.79/0.87  fof(f4,axiom,(
% 3.79/0.87    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 3.79/0.87  fof(f3502,plain,(
% 3.79/0.87    k1_tarski(sK1) != k2_tarski(sK1,sK1) | (spl5_1 | ~spl5_3 | ~spl5_55)),
% 3.79/0.87    inference(backward_demodulation,[],[f2284,f3433])).
% 3.79/0.87  fof(f3433,plain,(
% 3.79/0.87    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_55),
% 3.79/0.87    inference(avatar_component_clause,[],[f3431])).
% 3.79/0.87  fof(f3431,plain,(
% 3.79/0.87    spl5_55 <=> sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 3.79/0.87  fof(f2284,plain,(
% 3.79/0.87    k1_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)) != k2_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK1) | (spl5_1 | ~spl5_3)),
% 3.79/0.87    inference(resolution,[],[f1340,f1737])).
% 3.79/0.87  fof(f1737,plain,(
% 3.79/0.87    ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | (spl5_1 | ~spl5_3)),
% 3.79/0.87    inference(subsumption_resolution,[],[f1736,f1141])).
% 3.79/0.87  fof(f1141,plain,(
% 3.79/0.87    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,sK2)) ) | ~spl5_3),
% 3.79/0.87    inference(superposition,[],[f59,f931])).
% 3.79/0.87  fof(f931,plain,(
% 3.79/0.87    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2) | ~spl5_3),
% 3.79/0.87    inference(resolution,[],[f78,f50])).
% 3.79/0.87  fof(f50,plain,(
% 3.79/0.87    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f26])).
% 3.79/0.87  fof(f26,plain,(
% 3.79/0.87    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 3.79/0.87    inference(nnf_transformation,[],[f3])).
% 3.79/0.87  fof(f3,axiom,(
% 3.79/0.87    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 3.79/0.87  fof(f1736,plain,(
% 3.79/0.87    ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_1),
% 3.79/0.87    inference(equality_resolution,[],[f1079])).
% 3.79/0.87  fof(f1079,plain,(
% 3.79/0.87    ( ! [X1] : (k1_xboole_0 != X1 | ~r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),sK2) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X1),X1)) ) | spl5_1),
% 3.79/0.87    inference(superposition,[],[f71,f38])).
% 3.79/0.87  fof(f38,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f18])).
% 3.79/0.87  fof(f71,plain,(
% 3.79/0.87    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl5_1),
% 3.79/0.87    inference(avatar_component_clause,[],[f69])).
% 3.79/0.87  fof(f69,plain,(
% 3.79/0.87    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.79/0.87  fof(f1340,plain,(
% 3.79/0.87    ( ! [X0] : (r2_hidden(X0,sK2) | k1_tarski(X0) != k2_tarski(X0,sK1)) ) | ~spl5_3),
% 3.79/0.87    inference(subsumption_resolution,[],[f1331,f78])).
% 3.79/0.87  fof(f1331,plain,(
% 3.79/0.87    ( ! [X0] : (k1_tarski(X0) != k2_tarski(X0,sK1) | ~r2_hidden(sK1,sK2) | r2_hidden(X0,sK2)) ) | ~spl5_3),
% 3.79/0.87    inference(superposition,[],[f930,f53])).
% 3.79/0.87  fof(f53,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f28])).
% 3.79/0.87  fof(f930,plain,(
% 3.79/0.87    ( ! [X1] : (k2_tarski(X1,sK1) != k4_xboole_0(k2_tarski(X1,sK1),sK2)) ) | ~spl5_3),
% 3.79/0.87    inference(resolution,[],[f78,f41])).
% 3.79/0.87  fof(f41,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f20])).
% 3.79/0.87  fof(f3483,plain,(
% 3.79/0.87    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_54),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f3482])).
% 3.79/0.87  fof(f3482,plain,(
% 3.79/0.87    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_54)),
% 3.79/0.87    inference(subsumption_resolution,[],[f3453,f2727])).
% 3.79/0.87  fof(f2727,plain,(
% 3.79/0.87    k1_tarski(sK0) = k2_tarski(sK0,sK0) | ~spl5_2),
% 3.79/0.87    inference(subsumption_resolution,[],[f2719,f1057])).
% 3.79/0.87  fof(f1057,plain,(
% 3.79/0.87    ( ! [X6] : (~r2_hidden(sK0,k4_xboole_0(X6,sK2))) ) | ~spl5_2),
% 3.79/0.87    inference(resolution,[],[f74,f59])).
% 3.79/0.87  fof(f74,plain,(
% 3.79/0.87    r2_hidden(sK0,sK2) | ~spl5_2),
% 3.79/0.87    inference(avatar_component_clause,[],[f73])).
% 3.79/0.87  fof(f73,plain,(
% 3.79/0.87    spl5_2 <=> r2_hidden(sK0,sK2)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.79/0.87  fof(f2719,plain,(
% 3.79/0.87    ( ! [X2] : (k1_tarski(sK0) = k2_tarski(sK0,sK0) | r2_hidden(sK0,k4_xboole_0(X2,sK2))) ) | ~spl5_2),
% 3.79/0.87    inference(duplicate_literal_removal,[],[f2702])).
% 3.79/0.87  fof(f2702,plain,(
% 3.79/0.87    ( ! [X2] : (k1_tarski(sK0) = k2_tarski(sK0,sK0) | r2_hidden(sK0,k4_xboole_0(X2,sK2)) | r2_hidden(sK0,k4_xboole_0(X2,sK2))) ) | ~spl5_2),
% 3.79/0.87    inference(superposition,[],[f1112,f42])).
% 3.79/0.87  fof(f1112,plain,(
% 3.79/0.87    ( ! [X16] : (k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(X16,sK2))) ) | ~spl5_2),
% 3.79/0.87    inference(resolution,[],[f1057,f66])).
% 3.79/0.87  fof(f3453,plain,(
% 3.79/0.87    k1_tarski(sK0) != k2_tarski(sK0,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_54)),
% 3.79/0.87    inference(backward_demodulation,[],[f2327,f3429])).
% 3.79/0.87  fof(f3429,plain,(
% 3.79/0.87    sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_54),
% 3.79/0.87    inference(avatar_component_clause,[],[f3427])).
% 3.79/0.87  fof(f3427,plain,(
% 3.79/0.87    spl5_54 <=> sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 3.79/0.87  fof(f2327,plain,(
% 3.79/0.87    k1_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0)) != k2_tarski(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),sK0) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 3.79/0.87    inference(resolution,[],[f1478,f1737])).
% 3.79/0.87  fof(f1478,plain,(
% 3.79/0.87    ( ! [X0] : (r2_hidden(X0,sK2) | k1_tarski(X0) != k2_tarski(X0,sK0)) ) | ~spl5_2),
% 3.79/0.87    inference(subsumption_resolution,[],[f1469,f74])).
% 3.79/0.87  fof(f1469,plain,(
% 3.79/0.87    ( ! [X0] : (k1_tarski(X0) != k2_tarski(X0,sK0) | ~r2_hidden(sK0,sK2) | r2_hidden(X0,sK2)) ) | ~spl5_2),
% 3.79/0.87    inference(superposition,[],[f1051,f53])).
% 3.79/0.87  fof(f1051,plain,(
% 3.79/0.87    ( ! [X1] : (k2_tarski(X1,sK0) != k4_xboole_0(k2_tarski(X1,sK0),sK2)) ) | ~spl5_2),
% 3.79/0.87    inference(resolution,[],[f74,f41])).
% 3.79/0.87  fof(f3434,plain,(
% 3.79/0.87    spl5_54 | spl5_55 | ~spl5_26),
% 3.79/0.87    inference(avatar_split_clause,[],[f3414,f1762,f3431,f3427])).
% 3.79/0.87  fof(f1762,plain,(
% 3.79/0.87    spl5_26 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1))),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 3.79/0.87  fof(f3414,plain,(
% 3.79/0.87    sK1 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | sK0 = sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0) | ~spl5_26),
% 3.79/0.87    inference(resolution,[],[f1764,f65])).
% 3.79/0.87  fof(f65,plain,(
% 3.79/0.87    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.79/0.87    inference(equality_resolution,[],[f43])).
% 3.79/0.87  fof(f43,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f25])).
% 3.79/0.87  fof(f25,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.79/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 3.79/0.87  fof(f24,plain,(
% 3.79/0.87    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.79/0.87    introduced(choice_axiom,[])).
% 3.79/0.87  fof(f23,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.79/0.87    inference(rectify,[],[f22])).
% 3.79/0.87  fof(f22,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.79/0.87    inference(flattening,[],[f21])).
% 3.79/0.87  fof(f21,plain,(
% 3.79/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.79/0.87    inference(nnf_transformation,[],[f2])).
% 3.79/0.87  fof(f2,axiom,(
% 3.79/0.87    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 3.79/0.87  fof(f1764,plain,(
% 3.79/0.87    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | ~spl5_26),
% 3.79/0.87    inference(avatar_component_clause,[],[f1762])).
% 3.79/0.87  fof(f2624,plain,(
% 3.79/0.87    ~spl5_3 | spl5_8 | ~spl5_25),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f2622])).
% 3.79/0.87  fof(f2622,plain,(
% 3.79/0.87    $false | (~spl5_3 | spl5_8 | ~spl5_25)),
% 3.79/0.87    inference(resolution,[],[f2580,f1760])).
% 3.79/0.87  fof(f1760,plain,(
% 3.79/0.87    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl5_25),
% 3.79/0.87    inference(avatar_component_clause,[],[f1758])).
% 3.79/0.87  fof(f1758,plain,(
% 3.79/0.87    spl5_25 <=> r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.79/0.87  fof(f2580,plain,(
% 3.79/0.87    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | (~spl5_3 | spl5_8)),
% 3.79/0.87    inference(subsumption_resolution,[],[f2575,f1140])).
% 3.79/0.87  fof(f1140,plain,(
% 3.79/0.87    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k1_tarski(sK1))) ) | ~spl5_3),
% 3.79/0.87    inference(superposition,[],[f60,f931])).
% 3.79/0.87  fof(f60,plain,(
% 3.79/0.87    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.79/0.87    inference(equality_resolution,[],[f34])).
% 3.79/0.87  fof(f34,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f18])).
% 3.79/0.87  fof(f2575,plain,(
% 3.79/0.87    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK1)) | ~r2_hidden(X1,k1_xboole_0)) ) | (~spl5_3 | spl5_8)),
% 3.79/0.87    inference(superposition,[],[f59,f2460])).
% 3.79/0.87  fof(f2460,plain,(
% 3.79/0.87    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_xboole_0) | (~spl5_3 | spl5_8)),
% 3.79/0.87    inference(backward_demodulation,[],[f962,f2459])).
% 3.79/0.87  fof(f962,plain,(
% 3.79/0.87    k1_tarski(sK1) = k4_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0) | spl5_8),
% 3.79/0.87    inference(resolution,[],[f192,f66])).
% 3.79/0.87  fof(f192,plain,(
% 3.79/0.87    ~r2_hidden(sK1,k1_xboole_0) | spl5_8),
% 3.79/0.87    inference(avatar_component_clause,[],[f190])).
% 3.79/0.87  fof(f190,plain,(
% 3.79/0.87    spl5_8 <=> r2_hidden(sK1,k1_xboole_0)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.79/0.87  fof(f1765,plain,(
% 3.79/0.87    spl5_25 | spl5_26 | spl5_1),
% 3.79/0.87    inference(avatar_split_clause,[],[f1756,f69,f1762,f1758])).
% 3.79/0.87  fof(f1756,plain,(
% 3.79/0.87    r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | spl5_1),
% 3.79/0.87    inference(equality_resolution,[],[f1078])).
% 3.79/0.87  fof(f1078,plain,(
% 3.79/0.87    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),k2_tarski(sK0,sK1)) | r2_hidden(sK3(k2_tarski(sK0,sK1),sK2,X0),X0)) ) | spl5_1),
% 3.79/0.87    inference(superposition,[],[f71,f37])).
% 3.79/0.87  fof(f37,plain,(
% 3.79/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 3.79/0.87    inference(cnf_transformation,[],[f18])).
% 3.79/0.87  fof(f1047,plain,(
% 3.79/0.87    ~spl5_6),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f1041])).
% 3.79/0.87  fof(f1041,plain,(
% 3.79/0.87    $false | ~spl5_6),
% 3.79/0.87    inference(resolution,[],[f1031,f125])).
% 3.79/0.87  fof(f125,plain,(
% 3.79/0.87    r2_hidden(sK0,k1_xboole_0) | ~spl5_6),
% 3.79/0.87    inference(avatar_component_clause,[],[f124])).
% 3.79/0.87  fof(f124,plain,(
% 3.79/0.87    spl5_6 <=> r2_hidden(sK0,k1_xboole_0)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.79/0.87  fof(f1031,plain,(
% 3.79/0.87    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0)) ) | ~spl5_6),
% 3.79/0.87    inference(subsumption_resolution,[],[f1023,f125])).
% 3.79/0.87  fof(f1023,plain,(
% 3.79/0.87    ( ! [X11] : (~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X11,k1_xboole_0)) ) | ~spl5_6),
% 3.79/0.87    inference(superposition,[],[f946,f50])).
% 3.79/0.87  fof(f946,plain,(
% 3.79/0.87    ( ! [X6] : (~r2_hidden(sK0,k4_xboole_0(X6,k1_xboole_0))) ) | ~spl5_6),
% 3.79/0.87    inference(resolution,[],[f125,f59])).
% 3.79/0.87  fof(f920,plain,(
% 3.79/0.87    ~spl5_1 | spl5_2 | spl5_6),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f919])).
% 3.79/0.87  fof(f919,plain,(
% 3.79/0.87    $false | (~spl5_1 | spl5_2 | spl5_6)),
% 3.79/0.87    inference(subsumption_resolution,[],[f918,f64])).
% 3.79/0.87  fof(f64,plain,(
% 3.79/0.87    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 3.79/0.87    inference(equality_resolution,[],[f63])).
% 3.79/0.87  fof(f63,plain,(
% 3.79/0.87    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 3.79/0.87    inference(equality_resolution,[],[f44])).
% 3.79/0.87  fof(f44,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f25])).
% 3.79/0.87  fof(f918,plain,(
% 3.79/0.87    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (~spl5_1 | spl5_2 | spl5_6)),
% 3.79/0.87    inference(subsumption_resolution,[],[f908,f126])).
% 3.79/0.87  fof(f126,plain,(
% 3.79/0.87    ~r2_hidden(sK0,k1_xboole_0) | spl5_6),
% 3.79/0.87    inference(avatar_component_clause,[],[f124])).
% 3.79/0.87  fof(f908,plain,(
% 3.79/0.87    r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 3.79/0.87    inference(resolution,[],[f75,f220])).
% 3.79/0.87  fof(f220,plain,(
% 3.79/0.87    ( ! [X2] : (r2_hidden(X2,sK2) | r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k2_tarski(sK0,sK1))) ) | ~spl5_1),
% 3.79/0.87    inference(superposition,[],[f58,f70])).
% 3.79/0.87  fof(f70,plain,(
% 3.79/0.87    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 3.79/0.87    inference(avatar_component_clause,[],[f69])).
% 3.79/0.87  fof(f58,plain,(
% 3.79/0.87    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.79/0.87    inference(equality_resolution,[],[f36])).
% 3.79/0.87  fof(f36,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f18])).
% 3.79/0.87  fof(f75,plain,(
% 3.79/0.87    ~r2_hidden(sK0,sK2) | spl5_2),
% 3.79/0.87    inference(avatar_component_clause,[],[f73])).
% 3.79/0.87  fof(f870,plain,(
% 3.79/0.87    ~spl5_1 | spl5_3),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f864])).
% 3.79/0.87  fof(f864,plain,(
% 3.79/0.87    $false | (~spl5_1 | spl5_3)),
% 3.79/0.87    inference(resolution,[],[f821,f702])).
% 3.79/0.87  fof(f702,plain,(
% 3.79/0.87    r2_hidden(sK1,k1_xboole_0) | (~spl5_1 | spl5_3)),
% 3.79/0.87    inference(superposition,[],[f410,f70])).
% 3.79/0.87  fof(f410,plain,(
% 3.79/0.87    ( ! [X20] : (r2_hidden(sK1,k4_xboole_0(k2_tarski(X20,sK1),sK2))) ) | spl5_3),
% 3.79/0.87    inference(resolution,[],[f200,f62])).
% 3.79/0.87  fof(f62,plain,(
% 3.79/0.87    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 3.79/0.87    inference(equality_resolution,[],[f61])).
% 3.79/0.87  fof(f61,plain,(
% 3.79/0.87    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 3.79/0.87    inference(equality_resolution,[],[f45])).
% 3.79/0.87  fof(f45,plain,(
% 3.79/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.79/0.87    inference(cnf_transformation,[],[f25])).
% 3.79/0.87  fof(f200,plain,(
% 3.79/0.87    ( ! [X5] : (~r2_hidden(sK1,X5) | r2_hidden(sK1,k4_xboole_0(X5,sK2))) ) | spl5_3),
% 3.79/0.87    inference(resolution,[],[f79,f58])).
% 3.79/0.87  fof(f79,plain,(
% 3.79/0.87    ~r2_hidden(sK1,sK2) | spl5_3),
% 3.79/0.87    inference(avatar_component_clause,[],[f77])).
% 3.79/0.87  fof(f821,plain,(
% 3.79/0.87    ( ! [X11] : (~r2_hidden(X11,k1_xboole_0)) ) | (~spl5_1 | spl5_3)),
% 3.79/0.87    inference(subsumption_resolution,[],[f812,f702])).
% 3.79/0.87  fof(f812,plain,(
% 3.79/0.87    ( ! [X11] : (~r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X11,k1_xboole_0)) ) | (~spl5_1 | spl5_3)),
% 3.79/0.87    inference(superposition,[],[f737,f50])).
% 3.79/0.87  fof(f737,plain,(
% 3.79/0.87    ( ! [X6] : (~r2_hidden(sK1,k4_xboole_0(X6,k1_xboole_0))) ) | (~spl5_1 | spl5_3)),
% 3.79/0.87    inference(resolution,[],[f702,f59])).
% 3.79/0.87  fof(f193,plain,(
% 3.79/0.87    spl5_4 | ~spl5_8 | ~spl5_3),
% 3.79/0.87    inference(avatar_split_clause,[],[f184,f77,f190,f117])).
% 3.79/0.87  fof(f117,plain,(
% 3.79/0.87    spl5_4 <=> ! [X7] : ~r2_hidden(X7,sK2)),
% 3.79/0.87    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.79/0.87  fof(f184,plain,(
% 3.79/0.87    ( ! [X11] : (~r2_hidden(sK1,k1_xboole_0) | ~r2_hidden(X11,sK2)) ) | ~spl5_3),
% 3.79/0.87    inference(superposition,[],[f98,f50])).
% 3.79/0.87  fof(f98,plain,(
% 3.79/0.87    ( ! [X6] : (~r2_hidden(sK1,k4_xboole_0(X6,sK2))) ) | ~spl5_3),
% 3.79/0.87    inference(resolution,[],[f78,f59])).
% 3.79/0.87  fof(f156,plain,(
% 3.79/0.87    ~spl5_2 | ~spl5_4),
% 3.79/0.87    inference(avatar_contradiction_clause,[],[f148])).
% 3.79/0.87  fof(f148,plain,(
% 3.79/0.87    $false | (~spl5_2 | ~spl5_4)),
% 3.79/0.87    inference(resolution,[],[f118,f74])).
% 3.79/0.87  fof(f118,plain,(
% 3.79/0.87    ( ! [X7] : (~r2_hidden(X7,sK2)) ) | ~spl5_4),
% 3.79/0.87    inference(avatar_component_clause,[],[f117])).
% 3.79/0.87  fof(f82,plain,(
% 3.79/0.87    spl5_1 | spl5_2),
% 3.79/0.87    inference(avatar_split_clause,[],[f31,f73,f69])).
% 3.79/0.87  fof(f31,plain,(
% 3.79/0.87    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.79/0.87    inference(cnf_transformation,[],[f13])).
% 3.79/0.87  fof(f13,plain,(
% 3.79/0.87    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 3.79/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 3.79/0.87  fof(f12,plain,(
% 3.79/0.87    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 3.79/0.87    introduced(choice_axiom,[])).
% 3.79/0.87  fof(f11,plain,(
% 3.79/0.87    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(flattening,[],[f10])).
% 3.79/0.87  fof(f10,plain,(
% 3.79/0.87    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.79/0.87    inference(nnf_transformation,[],[f9])).
% 3.79/0.87  fof(f9,plain,(
% 3.79/0.87    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.79/0.87    inference(ennf_transformation,[],[f8])).
% 3.79/0.87  fof(f8,negated_conjecture,(
% 3.79/0.87    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.79/0.87    inference(negated_conjecture,[],[f7])).
% 3.79/0.87  fof(f7,conjecture,(
% 3.79/0.87    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.79/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 3.79/0.87  fof(f81,plain,(
% 3.79/0.87    spl5_1 | spl5_3),
% 3.79/0.87    inference(avatar_split_clause,[],[f32,f77,f69])).
% 3.79/0.87  fof(f32,plain,(
% 3.79/0.87    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.79/0.87    inference(cnf_transformation,[],[f13])).
% 3.79/0.87  fof(f80,plain,(
% 3.79/0.87    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 3.79/0.87    inference(avatar_split_clause,[],[f33,f77,f73,f69])).
% 3.79/0.87  fof(f33,plain,(
% 3.79/0.87    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 3.79/0.87    inference(cnf_transformation,[],[f13])).
% 3.79/0.87  % SZS output end Proof for theBenchmark
% 3.79/0.87  % (12902)------------------------------
% 3.79/0.87  % (12902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.79/0.87  % (12902)Termination reason: Refutation
% 3.79/0.87  
% 3.79/0.87  % (12902)Memory used [KB]: 12537
% 3.79/0.87  % (12902)Time elapsed: 0.437 s
% 3.79/0.87  % (12902)------------------------------
% 3.79/0.87  % (12902)------------------------------
% 3.79/0.88  % (12889)Success in time 0.515 s
%------------------------------------------------------------------------------
