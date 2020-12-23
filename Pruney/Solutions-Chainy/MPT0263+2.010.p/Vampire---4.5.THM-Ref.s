%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:13 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 152 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 782 expanded)
%              Number of equality atoms :   62 ( 190 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f158,f530,f533,f1379])).

fof(f1379,plain,
    ( ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1378])).

fof(f1378,plain,
    ( $false
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f1375,f324])).

fof(f324,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl5_3
  <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1375,plain,
    ( ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)
    | spl5_5 ),
    inference(superposition,[],[f571,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f571,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k3_xboole_0(k1_tarski(sK0),X0))
    | spl5_5 ),
    inference(resolution,[],[f339,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

% (19302)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% (19303)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f339,plain,
    ( ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f533,plain,
    ( spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f342,f337,f322])).

fof(f342,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f65,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    k1_xboole_0 != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f32,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f530,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f528,f194])).

fof(f194,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_1
    | spl5_2 ),
    inference(superposition,[],[f139,f172])).

fof(f172,plain,
    ( sK0 = sK3(k1_tarski(sK0),sK1,k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f136,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f136,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_1
  <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f139,plain,
    ( ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f528,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f527,f65])).

fof(f527,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f503,f234])).

fof(f234,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1
    | spl5_2 ),
    inference(superposition,[],[f214,f41])).

fof(f214,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k3_xboole_0(sK1,X0))
    | ~ spl5_1
    | spl5_2 ),
    inference(resolution,[],[f194,f59])).

fof(f503,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl5_5 ),
    inference(superposition,[],[f46,f474])).

fof(f474,plain,
    ( sK0 = sK3(k1_tarski(sK0),sK1,k1_xboole_0)
    | ~ spl5_5 ),
    inference(resolution,[],[f338,f56])).

fof(f338,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f337])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f158,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f154,f134])).

fof(f154,plain,(
    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f33,f45])).

fof(f33,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f149,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f148,f138,f134])).

fof(f148,plain,
    ( ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f147,f33])).

fof(f147,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f140,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f140,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:08:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (19254)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (19265)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (19260)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (19259)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (19273)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.53  % (19251)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (19265)Refutation not found, incomplete strategy% (19265)------------------------------
% 1.24/0.53  % (19265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (19265)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (19265)Memory used [KB]: 1663
% 1.24/0.53  % (19265)Time elapsed: 0.117 s
% 1.24/0.53  % (19265)------------------------------
% 1.24/0.53  % (19265)------------------------------
% 1.24/0.53  % (19272)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.24/0.54  % (19253)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.54  % (19252)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.54  % (19252)Refutation not found, incomplete strategy% (19252)------------------------------
% 1.24/0.54  % (19252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (19252)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (19252)Memory used [KB]: 1663
% 1.24/0.54  % (19252)Time elapsed: 0.125 s
% 1.24/0.54  % (19252)------------------------------
% 1.24/0.54  % (19252)------------------------------
% 1.24/0.54  % (19255)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.24/0.54  % (19256)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.54  % (19269)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.24/0.54  % (19257)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  % (19264)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.45/0.55  % (19262)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.45/0.55  % (19275)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.55  % (19276)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.45/0.55  % (19277)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (19275)Refutation not found, incomplete strategy% (19275)------------------------------
% 1.45/0.55  % (19275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (19275)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (19275)Memory used [KB]: 10618
% 1.45/0.55  % (19275)Time elapsed: 0.150 s
% 1.45/0.55  % (19275)------------------------------
% 1.45/0.55  % (19275)------------------------------
% 1.45/0.56  % (19279)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.45/0.56  % (19271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (19261)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.45/0.56  % (19263)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.45/0.56  % (19269)Refutation not found, incomplete strategy% (19269)------------------------------
% 1.45/0.56  % (19269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (19269)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (19269)Memory used [KB]: 1663
% 1.45/0.56  % (19269)Time elapsed: 0.150 s
% 1.45/0.56  % (19269)------------------------------
% 1.45/0.56  % (19269)------------------------------
% 1.45/0.56  % (19268)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.56  % (19270)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.56  % (19267)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.56  % (19267)Refutation not found, incomplete strategy% (19267)------------------------------
% 1.45/0.56  % (19267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (19267)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (19267)Memory used [KB]: 10618
% 1.45/0.56  % (19267)Time elapsed: 0.151 s
% 1.45/0.56  % (19267)------------------------------
% 1.45/0.56  % (19267)------------------------------
% 1.45/0.56  % (19278)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.45/0.57  % (19266)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.45/0.57  % (19277)Refutation not found, incomplete strategy% (19277)------------------------------
% 1.45/0.57  % (19277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (19277)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (19277)Memory used [KB]: 6268
% 1.45/0.57  % (19277)Time elapsed: 0.157 s
% 1.45/0.57  % (19277)------------------------------
% 1.45/0.57  % (19277)------------------------------
% 1.45/0.57  % (19268)Refutation not found, incomplete strategy% (19268)------------------------------
% 1.45/0.57  % (19268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (19268)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (19268)Memory used [KB]: 1663
% 1.45/0.57  % (19268)Time elapsed: 0.161 s
% 1.45/0.57  % (19268)------------------------------
% 1.45/0.57  % (19268)------------------------------
% 1.45/0.57  % (19280)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.45/0.57  % (19280)Refutation not found, incomplete strategy% (19280)------------------------------
% 1.45/0.57  % (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (19280)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (19280)Memory used [KB]: 1663
% 1.45/0.57  % (19280)Time elapsed: 0.162 s
% 1.45/0.57  % (19280)------------------------------
% 1.45/0.57  % (19280)------------------------------
% 1.45/0.57  % (19258)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.57  % (19278)Refutation not found, incomplete strategy% (19278)------------------------------
% 1.45/0.57  % (19278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (19278)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (19278)Memory used [KB]: 6140
% 1.45/0.57  % (19278)Time elapsed: 0.160 s
% 1.45/0.57  % (19278)------------------------------
% 1.45/0.57  % (19278)------------------------------
% 1.45/0.58  % (19274)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 2.04/0.65  % (19254)Refutation not found, incomplete strategy% (19254)------------------------------
% 2.04/0.65  % (19254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.65  % (19254)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.65  
% 2.04/0.65  % (19254)Memory used [KB]: 6140
% 2.04/0.65  % (19254)Time elapsed: 0.229 s
% 2.04/0.65  % (19254)------------------------------
% 2.04/0.65  % (19254)------------------------------
% 2.04/0.66  % (19263)Refutation found. Thanks to Tanya!
% 2.04/0.66  % SZS status Theorem for theBenchmark
% 2.04/0.66  % SZS output start Proof for theBenchmark
% 2.04/0.66  fof(f1380,plain,(
% 2.04/0.66    $false),
% 2.04/0.66    inference(avatar_sat_refutation,[],[f149,f158,f530,f533,f1379])).
% 2.04/0.66  fof(f1379,plain,(
% 2.04/0.66    ~spl5_3 | spl5_5),
% 2.04/0.66    inference(avatar_contradiction_clause,[],[f1378])).
% 2.04/0.66  fof(f1378,plain,(
% 2.04/0.66    $false | (~spl5_3 | spl5_5)),
% 2.04/0.66    inference(subsumption_resolution,[],[f1375,f324])).
% 2.04/0.66  fof(f324,plain,(
% 2.04/0.66    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) | ~spl5_3),
% 2.04/0.66    inference(avatar_component_clause,[],[f322])).
% 2.04/0.66  fof(f322,plain,(
% 2.04/0.66    spl5_3 <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 2.04/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.04/0.66  fof(f1375,plain,(
% 2.04/0.66    ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0) | spl5_5),
% 2.04/0.66    inference(superposition,[],[f571,f41])).
% 2.04/0.66  fof(f41,plain,(
% 2.04/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.04/0.66    inference(cnf_transformation,[],[f4])).
% 2.04/0.66  fof(f4,axiom,(
% 2.04/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.04/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.04/0.66  fof(f571,plain,(
% 2.04/0.66    ( ! [X0] : (~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k3_xboole_0(k1_tarski(sK0),X0))) ) | spl5_5),
% 2.04/0.66    inference(resolution,[],[f339,f59])).
% 2.04/0.66  fof(f59,plain,(
% 2.04/0.66    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(equality_resolution,[],[f42])).
% 2.04/0.66  fof(f42,plain,(
% 2.04/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.04/0.66    inference(cnf_transformation,[],[f26])).
% 2.04/0.66  fof(f26,plain,(
% 2.04/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 2.04/0.66  fof(f25,plain,(
% 2.04/0.66    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.04/0.66    introduced(choice_axiom,[])).
% 2.04/0.66  fof(f24,plain,(
% 2.04/0.66    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.66    inference(rectify,[],[f23])).
% 2.04/0.67  fof(f23,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(flattening,[],[f22])).
% 2.04/0.67  fof(f22,plain,(
% 2.04/0.67    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/0.67    inference(nnf_transformation,[],[f2])).
% 2.04/0.67  % (19302)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.68  % (19303)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.68  fof(f2,axiom,(
% 2.04/0.68    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.04/0.68  fof(f339,plain,(
% 2.04/0.68    ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | spl5_5),
% 2.04/0.68    inference(avatar_component_clause,[],[f337])).
% 2.04/0.68  fof(f337,plain,(
% 2.04/0.68    spl5_5 <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.04/0.68  fof(f533,plain,(
% 2.04/0.68    spl5_3 | spl5_5),
% 2.04/0.68    inference(avatar_split_clause,[],[f342,f337,f322])).
% 2.04/0.68  fof(f342,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_xboole_0)),
% 2.04/0.68    inference(equality_resolution,[],[f79])).
% 2.04/0.68  fof(f79,plain,(
% 2.04/0.68    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),X0)) )),
% 2.04/0.68    inference(superposition,[],[f65,f45])).
% 2.04/0.68  fof(f45,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f26])).
% 2.04/0.68  fof(f65,plain,(
% 2.04/0.68    k1_xboole_0 != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(resolution,[],[f32,f35])).
% 2.04/0.68  fof(f35,plain,(
% 2.04/0.68    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.04/0.68    inference(cnf_transformation,[],[f15])).
% 2.04/0.68  fof(f15,plain,(
% 2.04/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 2.04/0.68    inference(ennf_transformation,[],[f13])).
% 2.04/0.68  fof(f13,plain,(
% 2.04/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 2.04/0.68    inference(unused_predicate_definition_removal,[],[f3])).
% 2.04/0.68  fof(f3,axiom,(
% 2.04/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.04/0.68  fof(f32,plain,(
% 2.04/0.68    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(cnf_transformation,[],[f17])).
% 2.04/0.68  fof(f17,plain,(
% 2.04/0.68    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 2.04/0.68  fof(f16,plain,(
% 2.04/0.68    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 2.04/0.68    introduced(choice_axiom,[])).
% 2.04/0.68  fof(f14,plain,(
% 2.04/0.68    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.04/0.68    inference(ennf_transformation,[],[f12])).
% 2.04/0.68  fof(f12,negated_conjecture,(
% 2.04/0.68    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.04/0.68    inference(negated_conjecture,[],[f11])).
% 2.04/0.68  fof(f11,conjecture,(
% 2.04/0.68    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 2.04/0.68  fof(f530,plain,(
% 2.04/0.68    ~spl5_1 | spl5_2 | ~spl5_5),
% 2.04/0.68    inference(avatar_contradiction_clause,[],[f529])).
% 2.04/0.68  fof(f529,plain,(
% 2.04/0.68    $false | (~spl5_1 | spl5_2 | ~spl5_5)),
% 2.04/0.68    inference(subsumption_resolution,[],[f528,f194])).
% 2.04/0.68  fof(f194,plain,(
% 2.04/0.68    ~r2_hidden(sK0,sK1) | (~spl5_1 | spl5_2)),
% 2.04/0.68    inference(superposition,[],[f139,f172])).
% 2.04/0.68  fof(f172,plain,(
% 2.04/0.68    sK0 = sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)) | ~spl5_1),
% 2.04/0.68    inference(resolution,[],[f136,f56])).
% 2.04/0.68  fof(f56,plain,(
% 2.04/0.68    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.04/0.68    inference(equality_resolution,[],[f36])).
% 2.04/0.68  fof(f36,plain,(
% 2.04/0.68    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.04/0.68    inference(cnf_transformation,[],[f21])).
% 2.04/0.68  fof(f21,plain,(
% 2.04/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 2.04/0.68  fof(f20,plain,(
% 2.04/0.68    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.04/0.68    introduced(choice_axiom,[])).
% 2.04/0.68  fof(f19,plain,(
% 2.04/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.68    inference(rectify,[],[f18])).
% 2.04/0.68  fof(f18,plain,(
% 2.04/0.68    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.04/0.68    inference(nnf_transformation,[],[f6])).
% 2.04/0.68  fof(f6,axiom,(
% 2.04/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.04/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.04/0.68  fof(f136,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_1),
% 2.04/0.68    inference(avatar_component_clause,[],[f134])).
% 2.04/0.68  fof(f134,plain,(
% 2.04/0.68    spl5_1 <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.04/0.68  fof(f139,plain,(
% 2.04/0.68    ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | spl5_2),
% 2.04/0.68    inference(avatar_component_clause,[],[f138])).
% 2.04/0.68  fof(f138,plain,(
% 2.04/0.68    spl5_2 <=> r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1)),
% 2.04/0.68    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.04/0.68  fof(f528,plain,(
% 2.04/0.68    r2_hidden(sK0,sK1) | (~spl5_1 | spl5_2 | ~spl5_5)),
% 2.04/0.68    inference(subsumption_resolution,[],[f527,f65])).
% 2.04/0.68  fof(f527,plain,(
% 2.04/0.68    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1) | (~spl5_1 | spl5_2 | ~spl5_5)),
% 2.04/0.68    inference(subsumption_resolution,[],[f503,f234])).
% 2.04/0.68  fof(f234,plain,(
% 2.04/0.68    ~r2_hidden(sK0,k1_xboole_0) | (~spl5_1 | spl5_2)),
% 2.04/0.68    inference(superposition,[],[f214,f41])).
% 2.04/0.68  fof(f214,plain,(
% 2.04/0.68    ( ! [X0] : (~r2_hidden(sK0,k3_xboole_0(sK1,X0))) ) | (~spl5_1 | spl5_2)),
% 2.04/0.68    inference(resolution,[],[f194,f59])).
% 2.04/0.68  fof(f503,plain,(
% 2.04/0.68    r2_hidden(sK0,k1_xboole_0) | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1) | ~spl5_5),
% 2.04/0.68    inference(superposition,[],[f46,f474])).
% 2.04/0.68  fof(f474,plain,(
% 2.04/0.68    sK0 = sK3(k1_tarski(sK0),sK1,k1_xboole_0) | ~spl5_5),
% 2.04/0.68    inference(resolution,[],[f338,f56])).
% 2.04/0.68  fof(f338,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_xboole_0),k1_tarski(sK0)) | ~spl5_5),
% 2.04/0.68    inference(avatar_component_clause,[],[f337])).
% 2.04/0.68  fof(f46,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f26])).
% 2.04/0.68  fof(f158,plain,(
% 2.04/0.68    spl5_1),
% 2.04/0.68    inference(avatar_split_clause,[],[f154,f134])).
% 2.04/0.68  fof(f154,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.04/0.68    inference(duplicate_literal_removal,[],[f153])).
% 2.04/0.68  fof(f153,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.04/0.68    inference(equality_resolution,[],[f71])).
% 2.04/0.68  fof(f71,plain,(
% 2.04/0.68    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK3(k1_tarski(sK0),sK1,X0),X0)) )),
% 2.04/0.68    inference(superposition,[],[f33,f45])).
% 2.04/0.68  fof(f33,plain,(
% 2.04/0.68    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.04/0.68    inference(cnf_transformation,[],[f17])).
% 2.04/0.68  fof(f149,plain,(
% 2.04/0.68    ~spl5_1 | ~spl5_2),
% 2.04/0.68    inference(avatar_split_clause,[],[f148,f138,f134])).
% 2.04/0.68  fof(f148,plain,(
% 2.04/0.68    ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_2),
% 2.04/0.68    inference(subsumption_resolution,[],[f147,f33])).
% 2.04/0.68  fof(f147,plain,(
% 2.04/0.68    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_2),
% 2.04/0.68    inference(duplicate_literal_removal,[],[f142])).
% 2.04/0.68  fof(f142,plain,(
% 2.04/0.68    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_2),
% 2.04/0.68    inference(resolution,[],[f140,f47])).
% 2.04/0.68  fof(f47,plain,(
% 2.04/0.68    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.04/0.68    inference(cnf_transformation,[],[f26])).
% 2.04/0.68  fof(f140,plain,(
% 2.04/0.68    r2_hidden(sK3(k1_tarski(sK0),sK1,k1_tarski(sK0)),sK1) | ~spl5_2),
% 2.04/0.68    inference(avatar_component_clause,[],[f138])).
% 2.04/0.68  % SZS output end Proof for theBenchmark
% 2.04/0.68  % (19263)------------------------------
% 2.04/0.68  % (19263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (19263)Termination reason: Refutation
% 2.04/0.68  
% 2.04/0.68  % (19263)Memory used [KB]: 11513
% 2.04/0.68  % (19263)Time elapsed: 0.251 s
% 2.04/0.68  % (19263)------------------------------
% 2.04/0.68  % (19263)------------------------------
% 2.04/0.68  % (19250)Success in time 0.308 s
%------------------------------------------------------------------------------
