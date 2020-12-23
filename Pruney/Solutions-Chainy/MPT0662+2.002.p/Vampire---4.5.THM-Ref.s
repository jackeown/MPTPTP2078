%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:12 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 156 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  331 ( 625 expanded)
%              Number of equality atoms :   37 ( 102 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f130,f132,f137,f142,f178,f181,f190,f204,f214,f240])).

fof(f240,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_19
    | spl6_17 ),
    inference(avatar_split_clause,[],[f236,f187,f201,f139,f108,f94])).

fof(f94,plain,
    ( spl6_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f108,plain,
    ( spl6_6
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f139,plain,
    ( spl6_12
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f201,plain,
    ( spl6_19
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f187,plain,
    ( spl6_17
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f236,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl6_17 ),
    inference(resolution,[],[f189,f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).

% (11840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f189,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f214,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f185,f29])).

fof(f29,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f185,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl6_16
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f204,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_19
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f192,f134,f201,f74,f94])).

fof(f74,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f134,plain,
    ( spl6_11
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f192,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f136,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f136,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f190,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f128,f187,f183,f116,f108])).

fof(f116,plain,
    ( spl6_8
  <=> v1_funct_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f128,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f54,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k1_funct_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f38,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ~ sQ5_eqProxy(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k1_funct_1(sK2,sK0)) ),
    inference(equality_proxy_replacement,[],[f30,f53])).

fof(f30,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,
    ( ~ spl6_2
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl6_2
    | spl6_8 ),
    inference(resolution,[],[f118,f79])).

fof(f79,plain,
    ( ! [X2] : v1_funct_1(k7_relat_1(sK2,X2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> ! [X2] : v1_funct_1(k7_relat_1(sK2,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f118,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f178,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f110,f62])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f142,plain,
    ( ~ spl6_5
    | spl6_12 ),
    inference(avatar_split_clause,[],[f100,f139,f94])).

fof(f100,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f137,plain,
    ( ~ spl6_5
    | spl6_11 ),
    inference(avatar_split_clause,[],[f101,f134,f94])).

% (11838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f101,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f132,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f96,f27])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f130,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f129])).

% (11847)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f129,plain,
    ( $false
    | spl6_1 ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f97,plain,
    ( ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f90,f78,f94])).

fof(f90,plain,(
    ! [X1] :
      ( v1_funct_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f28,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:28:56 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.44  % (11839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.44  % (11845)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.45  % (11853)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.45  % (11853)Refutation not found, incomplete strategy% (11853)------------------------------
% 0.18/0.45  % (11853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (11853)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.45  
% 0.18/0.45  % (11853)Memory used [KB]: 10618
% 0.18/0.45  % (11853)Time elapsed: 0.063 s
% 0.18/0.45  % (11853)------------------------------
% 0.18/0.45  % (11853)------------------------------
% 0.18/0.45  % (11845)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f245,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(avatar_sat_refutation,[],[f97,f130,f132,f137,f142,f178,f181,f190,f204,f214,f240])).
% 0.18/0.45  fof(f240,plain,(
% 0.18/0.45    ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_19 | spl6_17),
% 0.18/0.45    inference(avatar_split_clause,[],[f236,f187,f201,f139,f108,f94])).
% 0.18/0.45  fof(f94,plain,(
% 0.18/0.45    spl6_5 <=> v1_relat_1(sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.18/0.45  fof(f108,plain,(
% 0.18/0.45    spl6_6 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.18/0.45  fof(f139,plain,(
% 0.18/0.45    spl6_12 <=> r2_hidden(sK0,sK1)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.18/0.45  fof(f201,plain,(
% 0.18/0.45    spl6_19 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.18/0.45  fof(f187,plain,(
% 0.18/0.45    spl6_17 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.18/0.45  fof(f236,plain,(
% 0.18/0.45    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~r2_hidden(sK0,sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl6_17),
% 0.18/0.45    inference(resolution,[],[f189,f47])).
% 0.18/0.45  fof(f47,plain,(
% 0.18/0.45    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(equality_resolution,[],[f33])).
% 0.18/0.45  fof(f33,plain,(
% 0.18/0.45    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f23])).
% 0.18/0.45  fof(f23,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).
% 0.18/0.45  % (11840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.45  fof(f22,plain,(
% 0.18/0.45    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f21,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(rectify,[],[f20])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(flattening,[],[f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(nnf_transformation,[],[f10])).
% 0.18/0.45  fof(f10,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.18/0.45  fof(f189,plain,(
% 0.18/0.45    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | spl6_17),
% 0.18/0.45    inference(avatar_component_clause,[],[f187])).
% 0.18/0.45  fof(f214,plain,(
% 0.18/0.45    spl6_16),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f209])).
% 0.18/0.45  fof(f209,plain,(
% 0.18/0.45    $false | spl6_16),
% 0.18/0.45    inference(resolution,[],[f185,f29])).
% 0.18/0.45  fof(f29,plain,(
% 0.18/0.45    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f9,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.18/0.45    inference(flattening,[],[f8])).
% 0.18/0.45  fof(f8,plain,(
% 0.18/0.45    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.18/0.45    inference(ennf_transformation,[],[f7])).
% 0.18/0.45  fof(f7,negated_conjecture,(
% 0.18/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.18/0.45    inference(negated_conjecture,[],[f6])).
% 0.18/0.45  fof(f6,conjecture,(
% 0.18/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 0.18/0.45  fof(f185,plain,(
% 0.18/0.45    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | spl6_16),
% 0.18/0.45    inference(avatar_component_clause,[],[f183])).
% 0.18/0.45  fof(f183,plain,(
% 0.18/0.45    spl6_16 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.18/0.45  fof(f204,plain,(
% 0.18/0.45    ~spl6_5 | ~spl6_1 | spl6_19 | ~spl6_11),
% 0.18/0.45    inference(avatar_split_clause,[],[f192,f134,f201,f74,f94])).
% 0.18/0.45  fof(f74,plain,(
% 0.18/0.45    spl6_1 <=> v1_funct_1(sK2)),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.18/0.45  fof(f134,plain,(
% 0.18/0.45    spl6_11 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.18/0.45  fof(f192,plain,(
% 0.18/0.45    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_11),
% 0.18/0.45    inference(resolution,[],[f136,f52])).
% 0.18/0.45  fof(f52,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(equality_resolution,[],[f37])).
% 0.18/0.45  fof(f37,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f24])).
% 0.18/0.45  fof(f24,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(nnf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(flattening,[],[f11])).
% 0.18/0.45  fof(f11,plain,(
% 0.18/0.45    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f4])).
% 0.18/0.45  fof(f4,axiom,(
% 0.18/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.18/0.45  fof(f136,plain,(
% 0.18/0.45    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl6_11),
% 0.18/0.45    inference(avatar_component_clause,[],[f134])).
% 0.18/0.45  fof(f190,plain,(
% 0.18/0.45    ~spl6_6 | ~spl6_8 | ~spl6_16 | ~spl6_17),
% 0.18/0.45    inference(avatar_split_clause,[],[f128,f187,f183,f116,f108])).
% 0.18/0.45  fof(f116,plain,(
% 0.18/0.45    spl6_8 <=> v1_funct_1(k7_relat_1(sK2,sK1))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.18/0.45  fof(f128,plain,(
% 0.18/0.45    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k7_relat_1(sK2,sK1)) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_funct_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.18/0.45    inference(resolution,[],[f54,f60])).
% 0.18/0.45  fof(f60,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (sQ5_eqProxy(k1_funct_1(X0,X1),X2) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(equality_proxy_replacement,[],[f38,f53])).
% 0.18/0.45  fof(f53,plain,(
% 0.18/0.45    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.18/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.18/0.45  fof(f38,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f24])).
% 0.18/0.45  fof(f54,plain,(
% 0.18/0.45    ~sQ5_eqProxy(k1_funct_1(k7_relat_1(sK2,sK1),sK0),k1_funct_1(sK2,sK0))),
% 0.18/0.45    inference(equality_proxy_replacement,[],[f30,f53])).
% 0.18/0.45  fof(f30,plain,(
% 0.18/0.45    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f181,plain,(
% 0.18/0.45    ~spl6_2 | spl6_8),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f179])).
% 0.18/0.45  fof(f179,plain,(
% 0.18/0.45    $false | (~spl6_2 | spl6_8)),
% 0.18/0.45    inference(resolution,[],[f118,f79])).
% 0.18/0.45  fof(f79,plain,(
% 0.18/0.45    ( ! [X2] : (v1_funct_1(k7_relat_1(sK2,X2))) ) | ~spl6_2),
% 0.18/0.45    inference(avatar_component_clause,[],[f78])).
% 0.18/0.45  fof(f78,plain,(
% 0.18/0.45    spl6_2 <=> ! [X2] : v1_funct_1(k7_relat_1(sK2,X2))),
% 0.18/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.18/0.45  fof(f118,plain,(
% 0.18/0.45    ~v1_funct_1(k7_relat_1(sK2,sK1)) | spl6_8),
% 0.18/0.45    inference(avatar_component_clause,[],[f116])).
% 0.18/0.45  fof(f178,plain,(
% 0.18/0.45    spl6_6),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f175])).
% 0.18/0.45  fof(f175,plain,(
% 0.18/0.45    $false | spl6_6),
% 0.18/0.45    inference(resolution,[],[f110,f62])).
% 0.18/0.45  fof(f62,plain,(
% 0.18/0.45    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.18/0.45    inference(resolution,[],[f27,f41])).
% 0.18/0.45  fof(f41,plain,(
% 0.18/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f13])).
% 0.18/0.45  fof(f13,plain,(
% 0.18/0.45    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(ennf_transformation,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.18/0.45  fof(f27,plain,(
% 0.18/0.45    v1_relat_1(sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f110,plain,(
% 0.18/0.45    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl6_6),
% 0.18/0.45    inference(avatar_component_clause,[],[f108])).
% 0.18/0.45  fof(f142,plain,(
% 0.18/0.45    ~spl6_5 | spl6_12),
% 0.18/0.45    inference(avatar_split_clause,[],[f100,f139,f94])).
% 0.18/0.45  fof(f100,plain,(
% 0.18/0.45    r2_hidden(sK0,sK1) | ~v1_relat_1(sK2)),
% 0.18/0.45    inference(resolution,[],[f29,f44])).
% 0.18/0.45  fof(f44,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f26])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(flattening,[],[f25])).
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(nnf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,plain,(
% 0.18/0.45    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.18/0.45  fof(f137,plain,(
% 0.18/0.45    ~spl6_5 | spl6_11),
% 0.18/0.45    inference(avatar_split_clause,[],[f101,f134,f94])).
% 0.18/0.45  % (11838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.45  fof(f101,plain,(
% 0.18/0.45    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.18/0.45    inference(resolution,[],[f29,f45])).
% 0.18/0.45  fof(f45,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f26])).
% 0.18/0.45  fof(f132,plain,(
% 0.18/0.45    spl6_5),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f131])).
% 0.18/0.45  fof(f131,plain,(
% 0.18/0.45    $false | spl6_5),
% 0.18/0.45    inference(resolution,[],[f96,f27])).
% 0.18/0.45  fof(f96,plain,(
% 0.18/0.45    ~v1_relat_1(sK2) | spl6_5),
% 0.18/0.45    inference(avatar_component_clause,[],[f94])).
% 0.18/0.45  fof(f130,plain,(
% 0.18/0.45    spl6_1),
% 0.18/0.45    inference(avatar_contradiction_clause,[],[f129])).
% 0.18/0.45  % (11847)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.45  fof(f129,plain,(
% 0.18/0.45    $false | spl6_1),
% 0.18/0.45    inference(resolution,[],[f76,f28])).
% 0.18/0.45  fof(f28,plain,(
% 0.18/0.45    v1_funct_1(sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f76,plain,(
% 0.18/0.45    ~v1_funct_1(sK2) | spl6_1),
% 0.18/0.45    inference(avatar_component_clause,[],[f74])).
% 0.18/0.45  fof(f97,plain,(
% 0.18/0.45    ~spl6_5 | spl6_2),
% 0.18/0.45    inference(avatar_split_clause,[],[f90,f78,f94])).
% 0.18/0.45  fof(f90,plain,(
% 0.18/0.45    ( ! [X1] : (v1_funct_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) )),
% 0.18/0.45    inference(resolution,[],[f28,f43])).
% 0.18/0.45  fof(f43,plain,(
% 0.18/0.45    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f15])).
% 0.18/0.45  fof(f15,plain,(
% 0.18/0.45    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.45    inference(flattening,[],[f14])).
% 0.18/0.45  fof(f14,plain,(
% 0.18/0.45    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.45    inference(ennf_transformation,[],[f5])).
% 0.18/0.45  fof(f5,axiom,(
% 0.18/0.45    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.18/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (11845)------------------------------
% 0.18/0.45  % (11845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (11845)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (11845)Memory used [KB]: 6268
% 0.18/0.45  % (11845)Time elapsed: 0.066 s
% 0.18/0.45  % (11845)------------------------------
% 0.18/0.45  % (11845)------------------------------
% 0.18/0.46  % (11832)Success in time 0.119 s
%------------------------------------------------------------------------------
