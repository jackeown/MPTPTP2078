%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0236+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 133 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 645 expanded)
%              Number of equality atoms :   53 ( 192 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f86,f117])).

fof(f117,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f108,f51])).

fof(f51,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f108,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f95,f33])).

fof(f33,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f1])).

% (2569)Refutation not found, incomplete strategy% (2569)------------------------------
% (2569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2569)Termination reason: Refutation not found, incomplete strategy

% (2569)Memory used [KB]: 6140
% (2569)Time elapsed: 0.095 s
% (2569)------------------------------
% (2569)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),X0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f94,f51])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),X0)
      | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( sK0 != X2
      | ~ r2_hidden(X3,k1_tarski(sK0))
      | ~ r2_hidden(sK1(k1_tarski(sK0),X2),X3)
      | ~ r2_hidden(sK1(k1_tarski(sK0),X2),X2) ) ),
    inference(superposition,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f9,f12,f11,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f18,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    sK0 != k3_tarski(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] : k3_tarski(k1_tarski(X0)) != X0
   => sK0 != k3_tarski(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k3_tarski(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f86,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f85])).

% (2573)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f85,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f84,f74])).

fof(f74,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f72,f18])).

fof(f72,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k3_tarski(k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | sK0 = k3_tarski(k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_2 ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,
    ( sK0 = sK2(k1_tarski(sK0),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_2
  <=> r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f76,f18])).

fof(f76,plain,
    ( sK0 = k3_tarski(k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r2_hidden(sK1(k1_tarski(sK0),sK0),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f74,f24])).

fof(f56,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f47,f53,f49])).

fof(f47,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | r2_hidden(sK1(k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(sK2(k1_tarski(sK0),X1),k1_tarski(sK0))
      | r2_hidden(sK1(k1_tarski(sK0),X1),X1) ) ),
    inference(superposition,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
