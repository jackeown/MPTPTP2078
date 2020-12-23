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
% DateTime   : Thu Dec  3 12:46:53 EST 2020

% Result     : Theorem 2.39s
% Output     : Refutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 159 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  313 ( 528 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1580,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f134,f139,f1176,f1211,f1579])).

fof(f1579,plain,
    ( ~ spl5_2
    | ~ spl5_9
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1578])).

fof(f1578,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_9
    | spl5_13 ),
    inference(subsumption_resolution,[],[f1561,f400])).

fof(f400,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl5_13
  <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1561,plain,
    ( r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1))
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f1052,f138])).

fof(f138,plain,
    ( r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_9
  <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1052,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,sK1))))
        | r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f63,f548])).

fof(f548,plain,
    ( ! [X6] : k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X6,k4_xboole_0(X6,sK1))))
    | ~ spl5_2 ),
    inference(superposition,[],[f160,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f160,plain,
    ( ! [X0] : k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f144,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f144,plain,
    ( ! [X0] : k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f77,f84,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f84,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f77,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f77,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
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
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1211,plain,
    ( ~ spl5_13
    | spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1182,f394,f131,f398])).

fof(f131,plain,
    ( spl5_8
  <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f394,plain,
    ( spl5_12
  <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1182,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1))
    | spl5_8
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f133,f395,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f37])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f395,plain,
    ( r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f394])).

fof(f133,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1176,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f1145,f136,f80,f394])).

fof(f80,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1145,plain,
    ( r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0))
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f138,f578])).

fof(f578,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X5))))
        | r2_hidden(X6,k1_relat_1(sK0)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f63,f183])).

fof(f183,plain,
    ( ! [X0] : k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f167,f55])).

fof(f167,plain,
    ( ! [X0] : k1_relat_1(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f82,f96,f34])).

fof(f96,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f82,f56])).

fof(f82,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f139,plain,
    ( spl5_9
    | spl5_1 ),
    inference(avatar_split_clause,[],[f120,f70,f136])).

fof(f70,plain,
    ( spl5_1
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f120,plain,
    ( r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,
    ( ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f134,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f121,f70,f131])).

fof(f121,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f72,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f78,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f53,f70])).

fof(f53,plain,(
    ~ r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f33,f37,f37])).

fof(f33,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (15531)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (15525)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15519)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.54  % (15516)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.44/0.54  % (15541)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.54  % (15520)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (15542)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.55  % (15518)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.55  % (15544)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (15512)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.56  % (15523)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.56  % (15537)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.56  % (15533)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.56  % (15532)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.57  % (15521)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.57  % (15528)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.57  % (15545)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.57  % (15536)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.57  % (15522)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.58  % (15540)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.58  % (15527)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.58  % (15524)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (15513)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.58  % (15517)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.58  % (15530)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.59  % (15546)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.59  % (15539)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.59  % (15514)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.60  % (15529)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.60  % (15538)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.39/0.68  % (15541)Refutation found. Thanks to Tanya!
% 2.39/0.68  % SZS status Theorem for theBenchmark
% 2.39/0.68  % SZS output start Proof for theBenchmark
% 2.39/0.68  fof(f1580,plain,(
% 2.39/0.68    $false),
% 2.39/0.68    inference(avatar_sat_refutation,[],[f73,f78,f83,f134,f139,f1176,f1211,f1579])).
% 2.39/0.68  fof(f1579,plain,(
% 2.39/0.68    ~spl5_2 | ~spl5_9 | spl5_13),
% 2.39/0.68    inference(avatar_contradiction_clause,[],[f1578])).
% 2.39/0.68  fof(f1578,plain,(
% 2.39/0.68    $false | (~spl5_2 | ~spl5_9 | spl5_13)),
% 2.39/0.68    inference(subsumption_resolution,[],[f1561,f400])).
% 2.39/0.68  fof(f400,plain,(
% 2.39/0.68    ~r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1)) | spl5_13),
% 2.39/0.68    inference(avatar_component_clause,[],[f398])).
% 2.39/0.68  fof(f398,plain,(
% 2.39/0.68    spl5_13 <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.39/0.68  fof(f1561,plain,(
% 2.39/0.68    r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1)) | (~spl5_2 | ~spl5_9)),
% 2.39/0.68    inference(resolution,[],[f1052,f138])).
% 2.39/0.68  fof(f138,plain,(
% 2.39/0.68    r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl5_9),
% 2.39/0.68    inference(avatar_component_clause,[],[f136])).
% 2.39/0.68  fof(f136,plain,(
% 2.39/0.68    spl5_9 <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.39/0.68  fof(f1052,plain,(
% 2.39/0.68    ( ! [X6,X5] : (~r2_hidden(X6,k1_relat_1(k4_xboole_0(X5,k4_xboole_0(X5,sK1)))) | r2_hidden(X6,k1_relat_1(sK1))) ) | ~spl5_2),
% 2.39/0.68    inference(superposition,[],[f63,f548])).
% 2.39/0.68  fof(f548,plain,(
% 2.39/0.68    ( ! [X6] : (k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(X6,k4_xboole_0(X6,sK1))))) ) | ~spl5_2),
% 2.39/0.68    inference(superposition,[],[f160,f54])).
% 2.39/0.68  fof(f54,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.39/0.68    inference(definition_unfolding,[],[f35,f37,f37])).
% 2.39/0.68  fof(f37,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.39/0.68    inference(cnf_transformation,[],[f6])).
% 2.39/0.68  fof(f6,axiom,(
% 2.39/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.39/0.68  fof(f35,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f1])).
% 2.39/0.68  fof(f1,axiom,(
% 2.39/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.39/0.68  fof(f160,plain,(
% 2.39/0.68    ( ! [X0] : (k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))) ) | ~spl5_2),
% 2.39/0.68    inference(forward_demodulation,[],[f144,f55])).
% 2.39/0.68  fof(f55,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.39/0.68    inference(definition_unfolding,[],[f36,f37])).
% 2.39/0.68  fof(f36,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.39/0.68    inference(cnf_transformation,[],[f5])).
% 2.39/0.68  fof(f5,axiom,(
% 2.39/0.68    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.39/0.68  fof(f144,plain,(
% 2.39/0.68    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))) ) | ~spl5_2),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f77,f84,f34])).
% 2.39/0.68  fof(f34,plain,(
% 2.39/0.68    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f13])).
% 2.39/0.68  fof(f13,plain,(
% 2.39/0.68    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.39/0.68    inference(ennf_transformation,[],[f8])).
% 2.39/0.68  fof(f8,axiom,(
% 2.39/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 2.39/0.68  fof(f84,plain,(
% 2.39/0.68    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) | ~spl5_2),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f77,f56])).
% 2.39/0.68  fof(f56,plain,(
% 2.39/0.68    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.39/0.68    inference(definition_unfolding,[],[f38,f37])).
% 2.39/0.68  fof(f38,plain,(
% 2.39/0.68    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f14])).
% 2.39/0.68  fof(f14,plain,(
% 2.39/0.68    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.39/0.68    inference(ennf_transformation,[],[f7])).
% 2.39/0.68  fof(f7,axiom,(
% 2.39/0.68    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.39/0.68  fof(f77,plain,(
% 2.39/0.68    v1_relat_1(sK1) | ~spl5_2),
% 2.39/0.68    inference(avatar_component_clause,[],[f75])).
% 2.39/0.68  fof(f75,plain,(
% 2.39/0.68    spl5_2 <=> v1_relat_1(sK1)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.39/0.68  fof(f63,plain,(
% 2.39/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 2.39/0.68    inference(equality_resolution,[],[f43])).
% 2.39/0.68  fof(f43,plain,(
% 2.39/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.39/0.68    inference(cnf_transformation,[],[f25])).
% 2.39/0.68  fof(f25,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 2.39/0.68  fof(f24,plain,(
% 2.39/0.68    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f23,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(rectify,[],[f22])).
% 2.39/0.68  fof(f22,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(flattening,[],[f21])).
% 2.39/0.68  fof(f21,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(nnf_transformation,[],[f3])).
% 2.39/0.68  fof(f3,axiom,(
% 2.39/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.39/0.68  fof(f1211,plain,(
% 2.39/0.68    ~spl5_13 | spl5_8 | ~spl5_12),
% 2.39/0.68    inference(avatar_split_clause,[],[f1182,f394,f131,f398])).
% 2.39/0.68  fof(f131,plain,(
% 2.39/0.68    spl5_8 <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.39/0.68  fof(f394,plain,(
% 2.39/0.68    spl5_12 <=> r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.39/0.68  fof(f1182,plain,(
% 2.39/0.68    ~r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK1)) | (spl5_8 | ~spl5_12)),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f133,f395,f66])).
% 2.39/0.68  fof(f66,plain,(
% 2.39/0.68    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.39/0.68    inference(equality_resolution,[],[f60])).
% 2.39/0.68  fof(f60,plain,(
% 2.39/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.39/0.68    inference(definition_unfolding,[],[f49,f37])).
% 2.39/0.68  fof(f49,plain,(
% 2.39/0.68    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.39/0.68    inference(cnf_transformation,[],[f30])).
% 2.39/0.68  fof(f30,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 2.39/0.68  fof(f29,plain,(
% 2.39/0.68    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f28,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(rectify,[],[f27])).
% 2.39/0.68  fof(f27,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(flattening,[],[f26])).
% 2.39/0.68  fof(f26,plain,(
% 2.39/0.68    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.39/0.68    inference(nnf_transformation,[],[f4])).
% 2.39/0.68  fof(f4,axiom,(
% 2.39/0.68    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.39/0.68  fof(f395,plain,(
% 2.39/0.68    r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0)) | ~spl5_12),
% 2.39/0.68    inference(avatar_component_clause,[],[f394])).
% 2.39/0.68  fof(f133,plain,(
% 2.39/0.68    ~r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) | spl5_8),
% 2.39/0.68    inference(avatar_component_clause,[],[f131])).
% 2.39/0.68  fof(f1176,plain,(
% 2.39/0.68    spl5_12 | ~spl5_3 | ~spl5_9),
% 2.39/0.68    inference(avatar_split_clause,[],[f1145,f136,f80,f394])).
% 2.39/0.68  fof(f80,plain,(
% 2.39/0.68    spl5_3 <=> v1_relat_1(sK0)),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.39/0.68  fof(f1145,plain,(
% 2.39/0.68    r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(sK0)) | (~spl5_3 | ~spl5_9)),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f138,f578])).
% 2.39/0.68  fof(f578,plain,(
% 2.39/0.68    ( ! [X6,X5] : (~r2_hidden(X6,k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X5)))) | r2_hidden(X6,k1_relat_1(sK0))) ) | ~spl5_3),
% 2.39/0.68    inference(superposition,[],[f63,f183])).
% 2.39/0.68  fof(f183,plain,(
% 2.39/0.68    ( ! [X0] : (k1_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) ) | ~spl5_3),
% 2.39/0.68    inference(forward_demodulation,[],[f167,f55])).
% 2.39/0.68  fof(f167,plain,(
% 2.39/0.68    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) ) | ~spl5_3),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f82,f96,f34])).
% 2.39/0.68  fof(f96,plain,(
% 2.39/0.68    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) ) | ~spl5_3),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f82,f56])).
% 2.39/0.68  fof(f82,plain,(
% 2.39/0.68    v1_relat_1(sK0) | ~spl5_3),
% 2.39/0.68    inference(avatar_component_clause,[],[f80])).
% 2.39/0.68  fof(f139,plain,(
% 2.39/0.68    spl5_9 | spl5_1),
% 2.39/0.68    inference(avatar_split_clause,[],[f120,f70,f136])).
% 2.39/0.68  fof(f70,plain,(
% 2.39/0.68    spl5_1 <=> r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 2.39/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.39/0.68  fof(f120,plain,(
% 2.39/0.68    r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl5_1),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f72,f39])).
% 2.39/0.68  fof(f39,plain,(
% 2.39/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f20])).
% 2.39/0.68  fof(f20,plain,(
% 2.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f19])).
% 2.39/0.68  fof(f19,plain,(
% 2.39/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f15,plain,(
% 2.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.39/0.68    inference(ennf_transformation,[],[f11])).
% 2.39/0.68  fof(f11,plain,(
% 2.39/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.39/0.68    inference(unused_predicate_definition_removal,[],[f2])).
% 2.39/0.68  fof(f2,axiom,(
% 2.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.39/0.68  fof(f72,plain,(
% 2.39/0.68    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) | spl5_1),
% 2.39/0.68    inference(avatar_component_clause,[],[f70])).
% 2.39/0.68  fof(f134,plain,(
% 2.39/0.68    ~spl5_8 | spl5_1),
% 2.39/0.68    inference(avatar_split_clause,[],[f121,f70,f131])).
% 2.39/0.68  fof(f121,plain,(
% 2.39/0.68    ~r2_hidden(sK2(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))) | spl5_1),
% 2.39/0.68    inference(unit_resulting_resolution,[],[f72,f40])).
% 2.39/0.68  fof(f40,plain,(
% 2.39/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.39/0.68    inference(cnf_transformation,[],[f20])).
% 2.39/0.68  fof(f83,plain,(
% 2.39/0.68    spl5_3),
% 2.39/0.68    inference(avatar_split_clause,[],[f31,f80])).
% 2.39/0.68  fof(f31,plain,(
% 2.39/0.68    v1_relat_1(sK0)),
% 2.39/0.68    inference(cnf_transformation,[],[f18])).
% 2.39/0.68  fof(f18,plain,(
% 2.39/0.68    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.39/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17,f16])).
% 2.39/0.68  fof(f16,plain,(
% 2.39/0.68    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f17,plain,(
% 2.39/0.68    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 2.39/0.68    introduced(choice_axiom,[])).
% 2.39/0.68  fof(f12,plain,(
% 2.39/0.68    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.39/0.68    inference(ennf_transformation,[],[f10])).
% 2.39/0.68  fof(f10,negated_conjecture,(
% 2.39/0.68    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 2.39/0.68    inference(negated_conjecture,[],[f9])).
% 2.39/0.68  fof(f9,conjecture,(
% 2.39/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 2.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 2.39/0.68  fof(f78,plain,(
% 2.39/0.68    spl5_2),
% 2.39/0.68    inference(avatar_split_clause,[],[f32,f75])).
% 2.39/0.68  fof(f32,plain,(
% 2.39/0.68    v1_relat_1(sK1)),
% 2.39/0.68    inference(cnf_transformation,[],[f18])).
% 2.39/0.68  fof(f73,plain,(
% 2.39/0.68    ~spl5_1),
% 2.39/0.68    inference(avatar_split_clause,[],[f53,f70])).
% 2.39/0.68  fof(f53,plain,(
% 2.39/0.68    ~r1_tarski(k1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k1_relat_1(sK0),k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))))),
% 2.39/0.68    inference(definition_unfolding,[],[f33,f37,f37])).
% 2.39/0.68  fof(f33,plain,(
% 2.39/0.68    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 2.39/0.68    inference(cnf_transformation,[],[f18])).
% 2.39/0.68  % SZS output end Proof for theBenchmark
% 2.39/0.68  % (15541)------------------------------
% 2.39/0.68  % (15541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.68  % (15541)Termination reason: Refutation
% 2.39/0.68  
% 2.39/0.68  % (15541)Memory used [KB]: 7419
% 2.39/0.68  % (15541)Time elapsed: 0.272 s
% 2.39/0.68  % (15541)------------------------------
% 2.39/0.68  % (15541)------------------------------
% 2.39/0.68  % (15510)Success in time 0.321 s
%------------------------------------------------------------------------------
