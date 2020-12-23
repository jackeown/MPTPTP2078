%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0056+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 196 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  308 (1133 expanded)
%              Number of equality atoms :   35 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f451,f704,f3153,f3171,f3195,f3235,f3238,f3244,f3247,f3248])).

fof(f3248,plain,
    ( ~ spl19_27
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f652,f453,f701])).

fof(f701,plain,
    ( spl19_27
  <=> r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_27])])).

fof(f453,plain,
    ( spl19_3
  <=> r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f652,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl19_3 ),
    inference(resolution,[],[f455,f348])).

fof(f348,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f314])).

fof(f314,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f192,f193])).

fof(f193,plain,(
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

fof(f192,plain,(
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
    inference(rectify,[],[f191])).

fof(f191,plain,(
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
    inference(flattening,[],[f190])).

fof(f190,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f455,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f453])).

fof(f3247,plain,
    ( ~ spl19_2
    | ~ spl19_3
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f3246,f444,f453,f448])).

fof(f448,plain,
    ( spl19_2
  <=> r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f444,plain,
    ( spl19_1
  <=> r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f3246,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f3172,f360])).

fof(f360,plain,(
    ~ sQ18_eqProxy(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f210,f356])).

fof(f356,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f210,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f103,f155])).

fof(f155,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f87])).

fof(f87,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f86])).

fof(f86,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3172,plain,
    ( sQ18_eqProxy(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl19_1 ),
    inference(resolution,[],[f446,f420])).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f324,f356])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f197,f198])).

fof(f198,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK14(X0,X1,X2),X1)
            & r2_hidden(sK14(X0,X1,X2),X0) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f196])).

fof(f196,plain,(
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
    inference(flattening,[],[f195])).

fof(f195,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f446,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f444])).

fof(f3244,plain,
    ( spl19_2
    | ~ spl19_26 ),
    inference(avatar_split_clause,[],[f3212,f697,f448])).

fof(f697,plain,
    ( spl19_26
  <=> r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_26])])).

fof(f3212,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl19_26 ),
    inference(resolution,[],[f698,f352])).

fof(f352,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f319])).

fof(f319,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f199])).

fof(f698,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ spl19_26 ),
    inference(avatar_component_clause,[],[f697])).

fof(f3238,plain,
    ( ~ spl19_27
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f3175,f444,f701])).

fof(f3175,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl19_1 ),
    inference(resolution,[],[f446,f348])).

fof(f3235,plain,
    ( spl19_3
    | ~ spl19_26
    | spl19_27 ),
    inference(avatar_contradiction_clause,[],[f3234])).

fof(f3234,plain,
    ( $false
    | spl19_3
    | ~ spl19_26
    | spl19_27 ),
    inference(subsumption_resolution,[],[f3213,f3169])).

fof(f3169,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | spl19_3
    | spl19_27 ),
    inference(subsumption_resolution,[],[f3154,f702])).

fof(f702,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | spl19_27 ),
    inference(avatar_component_clause,[],[f701])).

fof(f3154,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | spl19_3 ),
    inference(resolution,[],[f454,f347])).

fof(f347,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f315])).

fof(f315,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f454,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f453])).

fof(f3213,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl19_26 ),
    inference(resolution,[],[f698,f351])).

fof(f351,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f320])).

fof(f320,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f199])).

fof(f3195,plain,
    ( spl19_26
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f3174,f444,f697])).

fof(f3174,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | ~ spl19_1 ),
    inference(resolution,[],[f446,f349])).

fof(f349,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f313])).

fof(f313,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f3171,plain,
    ( spl19_1
    | spl19_3 ),
    inference(avatar_split_clause,[],[f3170,f453,f444])).

fof(f3170,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl19_3 ),
    inference(subsumption_resolution,[],[f3155,f360])).

fof(f3155,plain,
    ( sQ18_eqProxy(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl19_3 ),
    inference(resolution,[],[f454,f421])).

fof(f421,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f323,f356])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f199])).

fof(f3153,plain,
    ( ~ spl19_2
    | ~ spl19_3
    | spl19_26 ),
    inference(avatar_contradiction_clause,[],[f3152])).

fof(f3152,plain,
    ( $false
    | ~ spl19_2
    | ~ spl19_3
    | spl19_26 ),
    inference(subsumption_resolution,[],[f3151,f450])).

fof(f450,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f448])).

fof(f3151,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl19_3
    | spl19_26 ),
    inference(subsumption_resolution,[],[f3137,f651])).

fof(f651,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl19_3 ),
    inference(resolution,[],[f455,f349])).

fof(f3137,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | spl19_26 ),
    inference(resolution,[],[f699,f350])).

fof(f350,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f321])).

fof(f321,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f199])).

fof(f699,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | spl19_26 ),
    inference(avatar_component_clause,[],[f697])).

fof(f704,plain,
    ( ~ spl19_26
    | spl19_27
    | spl19_1 ),
    inference(avatar_split_clause,[],[f680,f444,f701,f697])).

fof(f680,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k3_xboole_0(sK0,sK1))
    | spl19_1 ),
    inference(resolution,[],[f445,f347])).

fof(f445,plain,
    ( ~ r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f444])).

fof(f451,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f429,f448,f444])).

fof(f429,plain,
    ( r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),sK0)
    | r2_hidden(sK14(sK0,k4_xboole_0(sK1,sK2),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(resolution,[],[f360,f422])).

fof(f422,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f322,f356])).

fof(f322,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f199])).
%------------------------------------------------------------------------------
