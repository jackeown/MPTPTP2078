%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0062+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 276 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  511 (1453 expanded)
%              Number of equality atoms :   51 ( 173 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3061,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f478,f1066,f1346,f1370,f1842,f1871,f1872,f1873,f1892,f2892,f2940,f2953,f2969,f2972,f2996,f3060])).

fof(f3060,plain,
    ( spl18_25
    | ~ spl18_52
    | ~ spl18_53 ),
    inference(avatar_contradiction_clause,[],[f3059])).

fof(f3059,plain,
    ( $false
    | spl18_25
    | ~ spl18_52
    | ~ spl18_53 ),
    inference(subsumption_resolution,[],[f3058,f1369])).

fof(f1369,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_53 ),
    inference(avatar_component_clause,[],[f1367])).

fof(f1367,plain,
    ( spl18_53
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_53])])).

fof(f3058,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl18_25
    | ~ spl18_52 ),
    inference(subsumption_resolution,[],[f3044,f1364])).

fof(f1364,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl18_52 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f1363,plain,
    ( spl18_52
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_52])])).

fof(f3044,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl18_25 ),
    inference(resolution,[],[f689,f361])).

fof(f361,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f329])).

fof(f329,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f201])).

fof(f201,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
            | ~ r2_hidden(sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f199,f200])).

fof(f200,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK12(X0,X1,X2),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK12(X0,X1,X2),X1)
            & r2_hidden(sK12(X0,X1,X2),X0) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f199,plain,(
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
    inference(rectify,[],[f198])).

fof(f198,plain,(
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
    inference(flattening,[],[f197])).

fof(f197,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f689,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl18_25 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl18_25
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_25])])).

fof(f2996,plain,
    ( ~ spl18_25
    | ~ spl18_1 ),
    inference(avatar_split_clause,[],[f2976,f465,f688])).

fof(f465,plain,
    ( spl18_1
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f2976,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl18_1 ),
    inference(resolution,[],[f467,f365])).

fof(f365,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f334])).

fof(f334,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f206])).

fof(f206,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f204,f205])).

fof(f205,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f204,plain,(
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
    inference(rectify,[],[f203])).

fof(f203,plain,(
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
    inference(flattening,[],[f202])).

fof(f202,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f467,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f465])).

fof(f2972,plain,
    ( spl18_1
    | spl18_2
    | spl18_3 ),
    inference(avatar_split_clause,[],[f2971,f473,f469,f465])).

fof(f469,plain,
    ( spl18_2
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f473,plain,
    ( spl18_3
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f2971,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl18_2
    | spl18_3 ),
    inference(subsumption_resolution,[],[f2970,f474])).

fof(f474,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | spl18_3 ),
    inference(avatar_component_clause,[],[f473])).

fof(f2970,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(subsumption_resolution,[],[f2955,f374])).

fof(f374,plain,(
    ~ sQ17_eqProxy(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f217,f370])).

fof(f370,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f217,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f163])).

fof(f163,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f110,f162])).

fof(f162,plain,
    ( ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ? [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f96])).

fof(f96,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f95])).

fof(f95,conjecture,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f2955,plain,
    ( sQ17_eqProxy(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl18_2 ),
    inference(resolution,[],[f470,f446])).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f342,f370])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f211])).

fof(f211,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & ~ r2_hidden(sK14(X0,X1,X2),X0) )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( r2_hidden(sK14(X0,X1,X2),X1)
            | r2_hidden(sK14(X0,X1,X2),X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f209,f210])).

fof(f210,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & ~ r2_hidden(sK14(X0,X1,X2),X0) )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( r2_hidden(sK14(X0,X1,X2),X1)
          | r2_hidden(sK14(X0,X1,X2),X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f209,plain,(
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
    inference(rectify,[],[f208])).

fof(f208,plain,(
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
    inference(flattening,[],[f207])).

fof(f207,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f470,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | spl18_2 ),
    inference(avatar_component_clause,[],[f469])).

fof(f2969,plain,
    ( ~ spl18_53
    | spl18_52
    | spl18_2 ),
    inference(avatar_split_clause,[],[f2954,f469,f1363,f1367])).

fof(f2954,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl18_2 ),
    inference(resolution,[],[f470,f364])).

fof(f364,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f335])).

fof(f335,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f206])).

fof(f2953,plain,
    ( spl18_53
    | spl18_52
    | ~ spl18_24 ),
    inference(avatar_split_clause,[],[f2895,f684,f1363,f1367])).

fof(f684,plain,
    ( spl18_24
  <=> r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_24])])).

fof(f2895,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_24 ),
    inference(resolution,[],[f685,f369])).

fof(f369,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f339])).

fof(f339,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f211])).

fof(f685,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl18_24 ),
    inference(avatar_component_clause,[],[f684])).

fof(f2940,plain,
    ( ~ spl18_25
    | spl18_52 ),
    inference(avatar_contradiction_clause,[],[f2939])).

fof(f2939,plain,
    ( $false
    | ~ spl18_25
    | spl18_52 ),
    inference(subsumption_resolution,[],[f2918,f1365])).

fof(f1365,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl18_52 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f2918,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl18_25 ),
    inference(resolution,[],[f690,f362])).

fof(f362,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f328])).

fof(f328,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f201])).

fof(f690,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl18_25 ),
    inference(avatar_component_clause,[],[f688])).

fof(f2892,plain,
    ( spl18_24
    | ~ spl18_53 ),
    inference(avatar_contradiction_clause,[],[f2891])).

fof(f2891,plain,
    ( $false
    | spl18_24
    | ~ spl18_53 ),
    inference(subsumption_resolution,[],[f2876,f1369])).

fof(f2876,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl18_24 ),
    inference(resolution,[],[f686,f368])).

fof(f368,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f340])).

fof(f340,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f211])).

fof(f686,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | spl18_24 ),
    inference(avatar_component_clause,[],[f684])).

fof(f1892,plain,
    ( ~ spl18_24
    | spl18_25
    | spl18_1 ),
    inference(avatar_split_clause,[],[f1877,f465,f688,f684])).

fof(f1877,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | spl18_1 ),
    inference(resolution,[],[f466,f364])).

fof(f466,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f465])).

fof(f1873,plain,
    ( ~ spl18_52
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1850,f469,f1363])).

fof(f1850,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl18_2 ),
    inference(resolution,[],[f471,f365])).

fof(f471,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f469])).

fof(f1872,plain,
    ( spl18_53
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1849,f469,f1367])).

fof(f1849,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl18_2 ),
    inference(resolution,[],[f471,f366])).

fof(f366,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f333])).

fof(f333,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f206])).

fof(f1871,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1870,f469,f465])).

fof(f1870,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f1848,f374])).

fof(f1848,plain,
    ( sQ17_eqProxy(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl18_2 ),
    inference(resolution,[],[f471,f445])).

fof(f445,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f343,f370])).

fof(f343,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f211])).

fof(f1842,plain,
    ( spl18_24
    | ~ spl18_1 ),
    inference(avatar_split_clause,[],[f1821,f465,f684])).

fof(f1821,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl18_1 ),
    inference(resolution,[],[f467,f366])).

fof(f1370,plain,
    ( ~ spl18_52
    | spl18_53
    | spl18_3 ),
    inference(avatar_split_clause,[],[f1347,f473,f1367,f1363])).

fof(f1347,plain,
    ( r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl18_3 ),
    inference(resolution,[],[f474,f364])).

fof(f1346,plain,
    ( ~ spl18_3
    | spl18_1
    | ~ spl18_5 ),
    inference(avatar_split_clause,[],[f1343,f484,f465,f473])).

fof(f484,plain,
    ( spl18_5
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f1343,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | spl18_1
    | ~ spl18_5 ),
    inference(resolution,[],[f1069,f466])).

fof(f1069,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
        | ~ r2_hidden(X0,k4_xboole_0(sK1,sK0)) )
    | ~ spl18_5 ),
    inference(resolution,[],[f485,f277])).

fof(f277,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f183,f184])).

fof(f184,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f485,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1066,plain,(
    spl18_5 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | spl18_5 ),
    inference(subsumption_resolution,[],[f1054,f359])).

fof(f359,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1054,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl18_5 ),
    inference(resolution,[],[f1044,f304])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1044,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | spl18_5 ),
    inference(subsumption_resolution,[],[f1034,f236])).

fof(f236,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1034,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | spl18_5 ),
    inference(resolution,[],[f486,f354])).

fof(f354,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f158])).

fof(f158,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f486,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl18_5 ),
    inference(avatar_component_clause,[],[f484])).

fof(f478,plain,
    ( ~ spl18_1
    | ~ spl18_3 ),
    inference(avatar_split_clause,[],[f452,f473,f465])).

fof(f452,plain,
    ( ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(sK1,sK0))
    | ~ r2_hidden(sK14(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f374,f444])).

fof(f444,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f344,f370])).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f211])).
%------------------------------------------------------------------------------
