%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0049+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:05 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 247 expanded)
%              Number of leaves         :   14 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 (1421 expanded)
%              Number of equality atoms :   35 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f431,f1873,f1875,f1876,f1909,f2175,f2176,f2177,f2178,f2179,f2223,f2225,f2246,f2328])).

fof(f2328,plain,
    ( spl19_3
    | ~ spl19_29
    | spl19_102 ),
    inference(avatar_contradiction_clause,[],[f2327])).

fof(f2327,plain,
    ( $false
    | spl19_3
    | ~ spl19_29
    | spl19_102 ),
    inference(subsumption_resolution,[],[f2326,f677])).

fof(f677,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl19_29 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl19_29
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_29])])).

fof(f2326,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | spl19_3
    | spl19_102 ),
    inference(subsumption_resolution,[],[f2312,f430])).

fof(f430,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | spl19_3 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl19_3
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f2312,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | spl19_102 ),
    inference(resolution,[],[f1906,f330])).

fof(f330,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f298])).

fof(f298,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f182,f183])).

fof(f183,plain,(
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

fof(f182,plain,(
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
    inference(rectify,[],[f181])).

fof(f181,plain,(
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
    inference(flattening,[],[f180])).

fof(f180,plain,(
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

fof(f1906,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | spl19_102 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1905,plain,
    ( spl19_102
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_102])])).

fof(f2246,plain,
    ( ~ spl19_102
    | spl19_1 ),
    inference(avatar_split_clause,[],[f2229,f419,f1905])).

fof(f419,plain,
    ( spl19_1
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2229,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | spl19_1 ),
    inference(resolution,[],[f420,f336])).

fof(f336,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f310])).

fof(f310,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f194,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f192,f193])).

fof(f193,plain,(
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

fof(f192,plain,(
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
    inference(rectify,[],[f191])).

fof(f191,plain,(
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
    inference(flattening,[],[f190])).

fof(f190,plain,(
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

fof(f420,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f419])).

fof(f2225,plain,
    ( spl19_28
    | spl19_29
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f2201,f423,f675,f671])).

fof(f671,plain,
    ( spl19_28
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_28])])).

fof(f423,plain,
    ( spl19_2
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f2201,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_2 ),
    inference(resolution,[],[f425,f338])).

fof(f338,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f308])).

fof(f308,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f425,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f423])).

fof(f2223,plain,
    ( ~ spl19_1
    | ~ spl19_2
    | spl19_3 ),
    inference(avatar_split_clause,[],[f2222,f428,f423,f419])).

fof(f2222,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl19_2
    | spl19_3 ),
    inference(subsumption_resolution,[],[f2221,f430])).

fof(f2221,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl19_2 ),
    inference(subsumption_resolution,[],[f2198,f342])).

fof(f342,plain,(
    ~ sQ18_eqProxy(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f200,f339])).

fof(f339,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f200,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f96,f145])).

fof(f145,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f80])).

fof(f80,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f79])).

fof(f79,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f2198,plain,
    ( sQ18_eqProxy(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl19_2 ),
    inference(resolution,[],[f425,f395])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f301,f339])).

fof(f301,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f2179,plain,
    ( ~ spl19_28
    | spl19_1
    | spl19_3 ),
    inference(avatar_split_clause,[],[f1852,f428,f419,f671])).

fof(f1852,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | spl19_1
    | spl19_3 ),
    inference(subsumption_resolution,[],[f1838,f430])).

fof(f1838,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | spl19_1 ),
    inference(resolution,[],[f716,f330])).

fof(f716,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | spl19_1 ),
    inference(resolution,[],[f420,f337])).

fof(f337,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f309])).

fof(f309,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f194])).

fof(f2178,plain,
    ( spl19_28
    | ~ spl19_101 ),
    inference(avatar_split_clause,[],[f2101,f1901,f671])).

fof(f1901,plain,
    ( spl19_101
  <=> r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_101])])).

fof(f2101,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl19_101 ),
    inference(resolution,[],[f1903,f332])).

fof(f332,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f296])).

fof(f296,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f1903,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl19_101 ),
    inference(avatar_component_clause,[],[f1901])).

fof(f2177,plain,
    ( ~ spl19_3
    | ~ spl19_101 ),
    inference(avatar_split_clause,[],[f2102,f1901,f428])).

fof(f2102,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_101 ),
    inference(resolution,[],[f1903,f331])).

fof(f331,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f297])).

fof(f297,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f184])).

fof(f2176,plain,
    ( spl19_29
    | ~ spl19_102 ),
    inference(avatar_split_clause,[],[f2148,f1905,f675])).

fof(f2148,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl19_102 ),
    inference(resolution,[],[f1907,f332])).

fof(f1907,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl19_102 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f2175,plain,
    ( ~ spl19_3
    | ~ spl19_102 ),
    inference(avatar_split_clause,[],[f2149,f1905,f428])).

fof(f2149,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl19_102 ),
    inference(resolution,[],[f1907,f331])).

fof(f1909,plain,
    ( spl19_101
    | spl19_102
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f1880,f419,f1905,f1901])).

fof(f1880,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl19_1 ),
    inference(resolution,[],[f421,f338])).

fof(f421,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f419])).

fof(f1876,plain,
    ( ~ spl19_28
    | spl19_2 ),
    inference(avatar_split_clause,[],[f1855,f423,f671])).

fof(f1855,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | spl19_2 ),
    inference(resolution,[],[f424,f337])).

fof(f424,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | spl19_2 ),
    inference(avatar_component_clause,[],[f423])).

fof(f1875,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f1874,f423,f419])).

fof(f1874,plain,
    ( r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | spl19_2 ),
    inference(subsumption_resolution,[],[f1857,f342])).

fof(f1857,plain,
    ( sQ18_eqProxy(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | spl19_2 ),
    inference(resolution,[],[f424,f397])).

fof(f397,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f299,f339])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f1873,plain,
    ( ~ spl19_29
    | spl19_2 ),
    inference(avatar_split_clause,[],[f1856,f423,f675])).

fof(f1856,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | spl19_2 ),
    inference(resolution,[],[f424,f336])).

fof(f431,plain,
    ( spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f408,f428,f419])).

fof(f408,plain,
    ( ~ r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK13(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f342,f396])).

fof(f396,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f300,f339])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f184])).
%------------------------------------------------------------------------------
