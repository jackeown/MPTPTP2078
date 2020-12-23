%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 131 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  264 ( 554 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f211,f231,f242,f244,f245,f278])).

fof(f278,plain,
    ( spl8_1
    | spl8_11
    | ~ spl8_12
    | ~ spl8_2
    | spl8_14 ),
    inference(avatar_split_clause,[],[f275,f209,f49,f198,f195,f45])).

fof(f45,plain,
    ( spl8_1
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f195,plain,
    ( spl8_11
  <=> ! [X6] : ~ r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f198,plain,
    ( spl8_12
  <=> r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f49,plain,
    ( spl8_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f209,plain,
    ( spl8_14
  <=> r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f275,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X3,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) )
    | ~ spl8_2
    | spl8_14 ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X3,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
        | ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) )
    | ~ spl8_2
    | spl8_14 ),
    inference(resolution,[],[f267,f62])).

fof(f62,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3))
        | ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),k1_relat_1(sK0)) )
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),k1_relat_1(sK0))
        | ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),X3)
        | ~ r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | k2_relat_1(sK0) = k9_relat_1(sK0,X3)
        | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

% (14884)Refutation not found, incomplete strategy% (14884)------------------------------
% (14884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14884)Termination reason: Refutation not found, incomplete strategy

% (14884)Memory used [KB]: 6140
% (14884)Time elapsed: 0.067 s
% (14884)------------------------------
% (14884)------------------------------
fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f57,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK1(X1,k9_relat_1(sK0,X2))),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X2))),X1)
        | k2_relat_1(X1) = k9_relat_1(sK0,X2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k9_relat_1(sK0,X1))
        | ~ r2_hidden(k4_tarski(X0,X2),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f267,plain,
    ( ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f245,plain,
    ( spl8_14
    | spl8_1
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f233,f195,f45,f209])).

fof(f233,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl8_11 ),
    inference(resolution,[],[f196,f30])).

fof(f196,plain,
    ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f195])).

fof(f244,plain,
    ( ~ spl8_14
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl8_14
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f210,f241])).

fof(f241,plain,
    ( ! [X0] : ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_17
  <=> ! [X0] : ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f210,plain,
    ( r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f242,plain,
    ( ~ spl8_2
    | spl8_17
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f234,f195,f240,f49])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f196,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f231,plain,
    ( spl8_1
    | spl8_11
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f224,f209,f195,f45])).

fof(f224,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) )
    | ~ spl8_14 ),
    inference(resolution,[],[f210,f31])).

fof(f211,plain,
    ( spl8_14
    | spl8_1
    | spl8_12 ),
    inference(avatar_split_clause,[],[f206,f198,f45,f209])).

fof(f206,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | spl8_12 ),
    inference(resolution,[],[f205,f30])).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)
    | spl8_12 ),
    inference(resolution,[],[f199,f42])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (14891)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f199,plain,
    ( ~ r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f198])).

fof(f51,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f47,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (14890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (14885)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14889)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14885)Refutation not found, incomplete strategy% (14885)------------------------------
% 0.21/0.49  % (14885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14885)Memory used [KB]: 10490
% 0.21/0.49  % (14885)Time elapsed: 0.069 s
% 0.21/0.49  % (14885)------------------------------
% 0.21/0.49  % (14885)------------------------------
% 0.21/0.49  % (14904)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (14892)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (14884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (14890)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f47,f51,f211,f231,f242,f244,f245,f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl8_1 | spl8_11 | ~spl8_12 | ~spl8_2 | spl8_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f275,f209,f49,f198,f195,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl8_1 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl8_11 <=> ! [X6] : ~r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl8_12 <=> r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl8_2 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl8_14 <=> r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X3,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))) ) | (~spl8_2 | spl8_14)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X3,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))) ) | (~spl8_2 | spl8_14)),
% 0.21/0.49    inference(resolution,[],[f267,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X4,X3] : (r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3)) | ~r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,X3) | ~r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),k1_relat_1(sK0))) ) | ~spl8_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),k1_relat_1(sK0)) | ~r2_hidden(sK2(sK0,k9_relat_1(sK0,X3)),X3) | ~r2_hidden(k4_tarski(X4,sK1(sK0,k9_relat_1(sK0,X3))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,X3) | k2_relat_1(sK0) = k9_relat_1(sK0,X3) | r2_hidden(sK1(sK0,k9_relat_1(sK0,X3)),k9_relat_1(sK0,X3))) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f57,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (14884)Refutation not found, incomplete strategy% (14884)------------------------------
% 0.21/0.49  % (14884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14884)Memory used [KB]: 6140
% 0.21/0.49  % (14884)Time elapsed: 0.067 s
% 0.21/0.49  % (14884)------------------------------
% 0.21/0.49  % (14884)------------------------------
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,sK1(X1,k9_relat_1(sK0,X2))),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X3,sK1(X1,k9_relat_1(sK0,X2))),X1) | k2_relat_1(X1) = k9_relat_1(sK0,X2)) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f56,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k9_relat_1(sK0,X1)) | ~r2_hidden(k4_tarski(X0,X2),sK0) | ~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(X0,X1)) ) | ~spl8_2),
% 0.21/0.49    inference(resolution,[],[f39,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl8_14 | spl8_1 | ~spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f233,f195,f45,f209])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | ~spl8_11),
% 0.21/0.49    inference(resolution,[],[f196,f30])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X6] : (~r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)) ) | ~spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f195])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~spl8_14 | ~spl8_17),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    $false | (~spl8_14 | ~spl8_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f210,f241])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0))) ) | ~spl8_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    spl8_17 <=> ! [X0] : ~r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | ~spl8_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~spl8_2 | spl8_17 | ~spl8_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f234,f195,f240,f49])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,X0)) | ~v1_relat_1(sK0)) ) | ~spl8_11),
% 0.21/0.49    inference(resolution,[],[f196,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl8_1 | spl8_11 | ~spl8_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f209,f195,f45])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X6] : (~r2_hidden(k4_tarski(X6,sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))) ) | ~spl8_14),
% 0.21/0.49    inference(resolution,[],[f210,f31])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl8_14 | spl8_1 | spl8_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f206,f198,f45,f209])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | r2_hidden(sK1(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | spl8_12),
% 0.21/0.49    inference(resolution,[],[f205,f30])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),X0),sK0)) ) | spl8_12),
% 0.21/0.49    inference(resolution,[],[f199,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f17,f20,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (14891)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~r2_hidden(sK2(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) | spl8_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f198])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0)) => (k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl8_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f45])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (14890)------------------------------
% 0.21/0.49  % (14890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14890)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (14890)Memory used [KB]: 10874
% 0.21/0.49  % (14890)Time elapsed: 0.064 s
% 0.21/0.49  % (14890)------------------------------
% 0.21/0.49  % (14890)------------------------------
% 0.21/0.49  % (14904)Refutation not found, incomplete strategy% (14904)------------------------------
% 0.21/0.49  % (14904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14904)Memory used [KB]: 10618
% 0.21/0.49  % (14904)Time elapsed: 0.072 s
% 0.21/0.49  % (14904)------------------------------
% 0.21/0.49  % (14904)------------------------------
% 0.21/0.50  % (14883)Success in time 0.134 s
%------------------------------------------------------------------------------
