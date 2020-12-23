%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0059+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 239 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  411 (1404 expanded)
%              Number of equality atoms :   47 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2485,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f460,f709,f2076,f2138,f2162,f2163,f2198,f2478,f2479,f2480,f2482,f2483,f2484])).

fof(f2484,plain,
    ( spl19_2
    | ~ spl19_103 ),
    inference(avatar_split_clause,[],[f2452,f2194,f457])).

fof(f457,plain,
    ( spl19_2
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f2194,plain,
    ( spl19_103
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_103])])).

fof(f2452,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_103 ),
    inference(resolution,[],[f2196,f360])).

fof(f360,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f327])).

fof(f327,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f203])).

fof(f203,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f201,f202])).

fof(f202,plain,(
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

fof(f201,plain,(
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
    inference(rectify,[],[f200])).

fof(f200,plain,(
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
    inference(flattening,[],[f199])).

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

fof(f2196,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl19_103 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f2483,plain,
    ( spl19_28
    | ~ spl19_103 ),
    inference(avatar_split_clause,[],[f2453,f2194,f706])).

fof(f706,plain,
    ( spl19_28
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_28])])).

fof(f2453,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_103 ),
    inference(resolution,[],[f2196,f359])).

fof(f359,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f328])).

fof(f328,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f203])).

fof(f2482,plain,
    ( ~ spl19_2
    | spl19_3
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2481,f453,f462,f457])).

fof(f462,plain,
    ( spl19_3
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f453,plain,
    ( spl19_1
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2481,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f2166,f368])).

fof(f368,plain,(
    ~ sQ18_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f214,f364])).

fof(f364,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f214,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f107,f159])).

fof(f159,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f93])).

fof(f93,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f92])).

fof(f92,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f2166,plain,
    ( sQ18_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_1 ),
    inference(resolution,[],[f455,f429])).

fof(f429,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f326,f364])).

fof(f326,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f196,f197])).

fof(f197,plain,(
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

fof(f196,plain,(
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
    inference(rectify,[],[f195])).

fof(f195,plain,(
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
    inference(flattening,[],[f194])).

fof(f194,plain,(
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
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f453])).

fof(f2480,plain,
    ( spl19_2
    | ~ spl19_102 ),
    inference(avatar_split_clause,[],[f2413,f2190,f457])).

fof(f2190,plain,
    ( spl19_102
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_102])])).

fof(f2413,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_102 ),
    inference(resolution,[],[f2192,f357])).

fof(f357,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f321])).

fof(f321,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f198])).

fof(f2192,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl19_102 ),
    inference(avatar_component_clause,[],[f2190])).

fof(f2479,plain,
    ( ~ spl19_27
    | ~ spl19_102 ),
    inference(avatar_split_clause,[],[f2414,f2190,f702])).

fof(f702,plain,
    ( spl19_27
  <=> r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_27])])).

fof(f2414,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_102 ),
    inference(resolution,[],[f2192,f356])).

fof(f356,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f322])).

fof(f322,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f198])).

fof(f2478,plain,
    ( spl19_27
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2140,f462,f702])).

fof(f2140,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_3 ),
    inference(resolution,[],[f463,f357])).

fof(f463,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f462])).

fof(f2198,plain,
    ( spl19_102
    | spl19_103
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2169,f453,f2194,f2190])).

fof(f2169,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl19_1 ),
    inference(resolution,[],[f455,f363])).

fof(f363,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f333])).

fof(f333,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f208])).

fof(f208,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
              & ~ r2_hidden(sK15(X0,X1,X2),X0) )
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( r2_hidden(sK15(X0,X1,X2),X1)
            | r2_hidden(sK15(X0,X1,X2),X0)
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f206,f207])).

fof(f207,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            & ~ r2_hidden(sK15(X0,X1,X2),X0) )
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( r2_hidden(sK15(X0,X1,X2),X1)
          | r2_hidden(sK15(X0,X1,X2),X0)
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f206,plain,(
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
    inference(rectify,[],[f205])).

fof(f205,plain,(
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
    inference(flattening,[],[f204])).

fof(f204,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2163,plain,
    ( ~ spl19_28
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2141,f462,f706])).

fof(f2141,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_3 ),
    inference(resolution,[],[f463,f356])).

fof(f2162,plain,
    ( spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2161,f462,f453])).

fof(f2161,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f2139,f368])).

fof(f2139,plain,
    ( sQ18_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(resolution,[],[f463,f430])).

fof(f430,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f325,f364])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).

fof(f2138,plain,
    ( spl19_1
    | ~ spl19_2
    | ~ spl19_28 ),
    inference(avatar_contradiction_clause,[],[f2137])).

fof(f2137,plain,
    ( $false
    | spl19_1
    | ~ spl19_2
    | ~ spl19_28 ),
    inference(subsumption_resolution,[],[f2136,f459])).

fof(f459,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f457])).

fof(f2136,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl19_1
    | ~ spl19_28 ),
    inference(subsumption_resolution,[],[f2122,f708])).

fof(f708,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_28 ),
    inference(avatar_component_clause,[],[f706])).

fof(f2122,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl19_1 ),
    inference(resolution,[],[f748,f358])).

fof(f358,plain,(
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
    inference(cnf_transformation,[],[f203])).

fof(f748,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl19_1 ),
    inference(resolution,[],[f454,f361])).

fof(f361,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f335])).

fof(f335,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f208])).

fof(f454,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f453])).

fof(f2076,plain,
    ( spl19_27
    | spl19_1
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f2075,f457,f453,f702])).

fof(f2075,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl19_1
    | ~ spl19_2 ),
    inference(subsumption_resolution,[],[f2058,f459])).

fof(f2058,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl19_1 ),
    inference(resolution,[],[f747,f355])).

fof(f355,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f323])).

fof(f323,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f198])).

fof(f747,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | spl19_1 ),
    inference(resolution,[],[f454,f362])).

fof(f362,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f334])).

fof(f334,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f208])).

fof(f709,plain,
    ( ~ spl19_27
    | spl19_28
    | spl19_3 ),
    inference(avatar_split_clause,[],[f686,f462,f706,f702])).

fof(f686,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl19_3 ),
    inference(resolution,[],[f464,f355])).

fof(f464,plain,
    ( ~ r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f462])).

fof(f460,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f441,f457,f453])).

fof(f441,plain,
    ( r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK13(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f368,f431])).

fof(f431,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f324,f364])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f198])).
%------------------------------------------------------------------------------
