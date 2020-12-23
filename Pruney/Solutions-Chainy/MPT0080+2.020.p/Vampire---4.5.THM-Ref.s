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
% DateTime   : Thu Dec  3 12:31:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 224 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  242 ( 949 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f226,f237,f259])).

fof(f259,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f250,f29])).

fof(f29,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK1,sK2)
    & r1_xboole_0(sK1,sK3)
    & r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK1,sK2)
      & r1_xboole_0(sK1,sK3)
      & r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f250,plain,
    ( r1_tarski(sK1,sK2)
    | spl6_5 ),
    inference(resolution,[],[f240,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f240,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl6_5 ),
    inference(resolution,[],[f164,f48])).

fof(f48,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f47,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f164,plain,
    ( ! [X2,X3] :
        ( ~ sP0(X2,X3,k2_xboole_0(sK1,sK2))
        | ~ r2_hidden(sK4(sK1,sK2),X2) )
    | spl6_5 ),
    inference(resolution,[],[f143,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & ~ r2_hidden(sK5(X0,X1,X2),X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & ~ r2_hidden(sK5(X0,X1,X2),X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f143,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_5
  <=> r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f237,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(resolution,[],[f227,f134])).

fof(f134,plain,
    ( r2_hidden(sK4(sK1,sK2),sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f227,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK3)
    | spl6_4 ),
    inference(resolution,[],[f157,f47])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( ~ sP0(X2,X3,k2_xboole_0(sK1,sK3))
        | ~ r2_hidden(sK4(sK1,sK2),X2) )
    | spl6_4 ),
    inference(resolution,[],[f139,f37])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f226,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f217,f29])).

fof(f217,plain,
    ( r1_tarski(sK1,sK2)
    | spl6_3 ),
    inference(resolution,[],[f207,f33])).

fof(f207,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl6_3 ),
    inference(resolution,[],[f173,f27])).

fof(f27,plain,(
    r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f173,plain,
    ( ! [X6] :
        ( ~ r1_tarski(X6,k2_xboole_0(sK2,sK3))
        | ~ r2_hidden(sK4(sK1,sK2),X6) )
    | spl6_3 ),
    inference(resolution,[],[f146,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f146,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK2,sK3))
    | spl6_3 ),
    inference(resolution,[],[f135,f76])).

fof(f76,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,sK2),X1)
      | ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK2,X1)) ) ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,(
    ! [X4,X5] :
      ( ~ sP0(sK2,X4,X5)
      | ~ r2_hidden(sK4(sK1,sK2),X5)
      | r2_hidden(sK4(sK1,sK2),X4) ) ),
    inference(resolution,[],[f35,f60])).

fof(f60,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ r2_hidden(sK4(sK1,sK2),X0) ) ),
    inference(resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK4(X0,X1),X2) ) ),
    inference(resolution,[],[f32,f34])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f145,plain,
    ( ~ spl6_5
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f126,f137,f133,f141])).

fof(f126,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK4(sK1,sK2),sK3)
    | ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,sK2),X0)
      | ~ r2_hidden(sK4(sK1,sK2),k2_xboole_0(X0,sK2)) ) ),
    inference(resolution,[],[f66,f47])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_xboole_0(sK1,sK3))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f46,f28])).

fof(f28,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (9884)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (9884)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (9892)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f145,f226,f237,f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    spl6_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    $false | spl6_5),
% 0.22/0.50    inference(resolution,[],[f250,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK2) & r1_xboole_0(sK1,sK3) & r1_tarski(sK1,k2_xboole_0(sK2,sK3))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f9,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK1,sK2) & r1_xboole_0(sK1,sK3) & r1_tarski(sK1,k2_xboole_0(sK2,sK3)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2) | spl6_5),
% 0.22/0.50    inference(resolution,[],[f240,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),sK1) | spl6_5),
% 0.22/0.50    inference(resolution,[],[f164,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(superposition,[],[f47,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.50    inference(definition_folding,[],[f3,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~sP0(X2,X3,k2_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(sK1,sK2),X2)) ) | spl6_5),
% 0.22/0.50    inference(resolution,[],[f143,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK5(X0,X1,X2),X0) & ~r2_hidden(sK5(X0,X1,X2),X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X0) & ~r2_hidden(sK5(X0,X1,X2),X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.50    inference(rectify,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2)) | spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl6_5 <=> r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ~spl6_3 | spl6_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f229])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    $false | (~spl6_3 | spl6_4)),
% 0.22/0.50    inference(resolution,[],[f227,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    r2_hidden(sK4(sK1,sK2),sK3) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl6_3 <=> r2_hidden(sK4(sK1,sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),sK3) | spl6_4),
% 0.22/0.50    inference(resolution,[],[f157,f47])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~sP0(X2,X3,k2_xboole_0(sK1,sK3)) | ~r2_hidden(sK4(sK1,sK2),X2)) ) | spl6_4),
% 0.22/0.50    inference(resolution,[],[f139,f37])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3)) | spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl6_4 <=> r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl6_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    $false | spl6_3),
% 0.22/0.50    inference(resolution,[],[f217,f29])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2) | spl6_3),
% 0.22/0.50    inference(resolution,[],[f207,f33])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),sK1) | spl6_3),
% 0.22/0.50    inference(resolution,[],[f173,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    r1_tarski(sK1,k2_xboole_0(sK2,sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X6] : (~r1_tarski(X6,k2_xboole_0(sK2,sK3)) | ~r2_hidden(sK4(sK1,sK2),X6)) ) | spl6_3),
% 0.22/0.50    inference(resolution,[],[f146,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK2,sK3)) | spl6_3),
% 0.22/0.50    inference(resolution,[],[f135,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(sK4(sK1,sK2),X1) | ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK2,X1))) )),
% 0.22/0.50    inference(resolution,[],[f66,f48])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~sP0(sK2,X4,X5) | ~r2_hidden(sK4(sK1,sK2),X5) | r2_hidden(sK4(sK1,sK2),X4)) )),
% 0.22/0.50    inference(resolution,[],[f35,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),sK2)),
% 0.22/0.50    inference(resolution,[],[f59,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f34,f33])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r2_hidden(sK4(sK1,sK2),X0)) )),
% 0.22/0.50    inference(resolution,[],[f54,f29])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK4(X0,X1),X2)) )),
% 0.22/0.50    inference(resolution,[],[f32,f34])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),sK3) | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~spl6_5 | ~spl6_3 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f126,f137,f133,f141])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK3)) | ~r2_hidden(sK4(sK1,sK2),sK3) | ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(resolution,[],[f122,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK4(sK1,sK2),X0) | ~r2_hidden(sK4(sK1,sK2),k2_xboole_0(X0,sK2))) )),
% 0.22/0.50    inference(resolution,[],[f66,f47])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_xboole_0(sK1,sK3)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.50    inference(resolution,[],[f46,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    r1_xboole_0(sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9884)------------------------------
% 0.22/0.50  % (9884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9884)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9884)Memory used [KB]: 6268
% 0.22/0.50  % (9884)Time elapsed: 0.072 s
% 0.22/0.50  % (9884)------------------------------
% 0.22/0.50  % (9884)------------------------------
% 0.22/0.50  % (9871)Success in time 0.145 s
%------------------------------------------------------------------------------
