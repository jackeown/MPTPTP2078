%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 218 expanded)
%              Number of leaves         :   13 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 (1364 expanded)
%              Number of equality atoms :   37 ( 174 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f830,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f135,f175,f290,f334,f376,f501,f596,f635,f653,f694,f699,f829])).

fof(f829,plain,
    ( spl5_8
    | spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f811,f160,f373,f696])).

fof(f696,plain,
    ( spl5_8
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f373,plain,
    ( spl5_7
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f160,plain,
    ( spl5_5
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f811,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f161,f36])).

% (9987)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f161,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f699,plain,
    ( ~ spl5_8
    | spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f655,f120,f164,f696])).

fof(f164,plain,
    ( spl5_6
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f120,plain,
    ( spl5_2
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f655,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | spl5_2 ),
    inference(resolution,[],[f122,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
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

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f122,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f694,plain,
    ( ~ spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f166,f117,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_1
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f166,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f653,plain,
    ( ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f121,f166,f32])).

fof(f121,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f635,plain,
    ( ~ spl5_5
    | spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f618,f116,f164,f160])).

fof(f618,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f118,f31])).

% (9993)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f118,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f596,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f117,f162,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f162,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f501,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f121,f272,f33])).

fof(f272,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)
    | spl5_5 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f376,plain,
    ( ~ spl5_7
    | spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f355,f132,f164,f373])).

fof(f132,plain,
    ( spl5_3
  <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f355,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | spl5_3 ),
    inference(resolution,[],[f134,f31])).

fof(f134,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f334,plain,
    ( ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f133,f166,f32])).

fof(f133,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f290,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl5_3
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f177,f162,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f177,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f133,f33])).

fof(f175,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f174,f132,f120,f116])).

fof(f174,plain,
    ( r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X0
      | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK2))
      | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK0,sK2))
      | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),X0) ) ),
    inference(superposition,[],[f18,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f135,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f130,f132,f116])).

fof(f130,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2] :
      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X2
      | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X2),k4_xboole_0(sK1,sK2))
      | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X2),X2) ) ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f114,f120,f116])).

fof(f114,plain,
    ( ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X1] :
      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X1
      | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X1),k4_xboole_0(sK0,sK2))
      | ~ r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X1),X1) ) ),
    inference(superposition,[],[f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (9989)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (9984)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (9980)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (9980)Refutation not found, incomplete strategy% (9980)------------------------------
% 0.20/0.47  % (9980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9980)Memory used [KB]: 10490
% 0.20/0.47  % (9980)Time elapsed: 0.061 s
% 0.20/0.47  % (9980)------------------------------
% 0.20/0.47  % (9980)------------------------------
% 0.20/0.47  % (9992)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (9992)Refutation not found, incomplete strategy% (9992)------------------------------
% 0.20/0.47  % (9992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9992)Memory used [KB]: 1535
% 0.20/0.47  % (9992)Time elapsed: 0.074 s
% 0.20/0.47  % (9992)------------------------------
% 0.20/0.47  % (9992)------------------------------
% 0.20/0.47  % (9989)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f830,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f123,f135,f175,f290,f334,f376,f501,f596,f635,f653,f694,f699,f829])).
% 0.20/0.47  fof(f829,plain,(
% 0.20/0.47    spl5_8 | spl5_7 | ~spl5_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f811,f160,f373,f696])).
% 0.20/0.47  fof(f696,plain,(
% 0.20/0.47    spl5_8 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    spl5_7 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl5_5 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.47  fof(f811,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1) | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0) | ~spl5_5),
% 0.20/0.47    inference(resolution,[],[f161,f36])).
% 0.20/0.47  % (9987)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(rectify,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1)) | ~spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f160])).
% 0.20/0.47  fof(f699,plain,(
% 0.20/0.47    ~spl5_8 | spl5_6 | spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f655,f120,f164,f696])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl5_6 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl5_2 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.47  fof(f655,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0) | spl5_2),
% 0.20/0.47    inference(resolution,[],[f122,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(rectify,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.47    inference(nnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) | spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f120])).
% 0.20/0.47  fof(f694,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f673])).
% 0.20/0.47  fof(f673,plain,(
% 0.20/0.47    $false | (~spl5_1 | ~spl5_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f166,f117,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl5_1 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) | ~spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f164])).
% 0.20/0.47  fof(f653,plain,(
% 0.20/0.47    ~spl5_2 | ~spl5_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f636])).
% 0.20/0.47  fof(f636,plain,(
% 0.20/0.47    $false | (~spl5_2 | ~spl5_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f121,f166,f32])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) | ~spl5_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f120])).
% 0.20/0.47  fof(f635,plain,(
% 0.20/0.47    ~spl5_5 | spl5_6 | spl5_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f618,f116,f164,f160])).
% 0.20/0.47  fof(f618,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1)) | spl5_1),
% 0.20/0.47    inference(resolution,[],[f118,f31])).
% 0.20/0.47  % (9993)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) | spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f596,plain,(
% 0.20/0.47    ~spl5_1 | spl5_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f577])).
% 0.20/0.47  fof(f577,plain,(
% 0.20/0.47    $false | (~spl5_1 | spl5_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f117,f162,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k2_xboole_0(sK0,sK1)) | spl5_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f160])).
% 0.20/0.47  fof(f501,plain,(
% 0.20/0.47    ~spl5_2 | spl5_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f481])).
% 0.20/0.47  fof(f481,plain,(
% 0.20/0.47    $false | (~spl5_2 | spl5_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f121,f272,f33])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK0) | spl5_5),
% 0.20/0.47    inference(resolution,[],[f162,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f376,plain,(
% 0.20/0.47    ~spl5_7 | spl5_6 | spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f355,f132,f164,f373])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl5_3 <=> r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f355,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK2) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1) | spl5_3),
% 0.20/0.47    inference(resolution,[],[f134,f31])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) | spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f132])).
% 0.20/0.47  fof(f334,plain,(
% 0.20/0.47    ~spl5_3 | ~spl5_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f314])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    $false | (~spl5_3 | ~spl5_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f133,f166,f32])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) | ~spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f132])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    ~spl5_3 | spl5_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f271])).
% 0.20/0.47  fof(f271,plain,(
% 0.20/0.47    $false | (~spl5_3 | spl5_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f177,f162,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),sK1) | ~spl5_3),
% 0.20/0.47    inference(resolution,[],[f133,f33])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl5_1 | spl5_2 | spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f174,f132,f120,f116])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 0.20/0.47    inference(equality_resolution,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X0 | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK2)) | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK0,sK2)) | r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X0),X0)) )),
% 0.20/0.47    inference(superposition,[],[f18,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f130,f132,f116])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 0.20/0.47    inference(equality_resolution,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2] : (k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X2 | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X2),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X2),X2)) )),
% 0.20/0.47    inference(superposition,[],[f18,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ~spl5_1 | ~spl5_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f114,f120,f116])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK2)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 0.20/0.47    inference(equality_resolution,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X1] : (k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != X1 | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X1),k4_xboole_0(sK0,sK2)) | ~r2_hidden(sK4(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2),X1),X1)) )),
% 0.20/0.47    inference(superposition,[],[f18,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (9989)------------------------------
% 0.20/0.47  % (9989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9989)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (9989)Memory used [KB]: 6524
% 0.20/0.47  % (9989)Time elapsed: 0.055 s
% 0.20/0.47  % (9989)------------------------------
% 0.20/0.47  % (9989)------------------------------
% 0.20/0.48  % (9978)Success in time 0.122 s
%------------------------------------------------------------------------------
