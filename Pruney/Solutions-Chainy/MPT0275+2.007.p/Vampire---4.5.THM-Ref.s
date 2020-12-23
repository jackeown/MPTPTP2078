%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 243 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 ( 625 expanded)
%              Number of equality atoms :   41 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f88,f96,f143,f148,f154,f161,f201,f206,f226,f287,f446,f447,f448,f449,f450,f455])).

fof(f455,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f453,f140,f79])).

fof(f79,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f140,plain,
    ( spl5_5
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f453,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f142,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f142,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f450,plain,
    ( spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f230,f198,f79])).

fof(f198,plain,
    ( spl5_7
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f230,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_7 ),
    inference(superposition,[],[f216,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f216,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK2,X0))
    | ~ spl5_7 ),
    inference(resolution,[],[f211,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f211,plain,
    ( ! [X0] : r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(sK2,X0))
    | ~ spl5_7 ),
    inference(resolution,[],[f207,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

% (9285)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(sK2,X0)) )
    | ~ spl5_7 ),
    inference(superposition,[],[f63,f200])).

fof(f200,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f198])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f449,plain,
    ( spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f233,f223,f79])).

fof(f223,plain,
    ( spl5_9
  <=> r1_tarski(k2_tarski(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f233,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f225,f67])).

fof(f225,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f223])).

fof(f448,plain,
    ( spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f234,f223,f79])).

fof(f234,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f225,f66])).

fof(f447,plain,
    ( spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f244,f198,f79])).

fof(f244,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_7 ),
    inference(superposition,[],[f231,f97])).

fof(f97,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f51,f47])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f231,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(X0,sK2))
    | ~ spl5_7 ),
    inference(superposition,[],[f216,f51])).

fof(f446,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f444,f140,f83,f79])).

fof(f83,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f444,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl5_5 ),
    inference(resolution,[],[f68,f141])).

fof(f141,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f287,plain,
    ( spl5_10
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f280,f203,f284])).

fof(f284,plain,
    ( spl5_10
  <=> r1_tarski(k2_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f203,plain,
    ( spl5_8
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f280,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),sK2)
    | ~ spl5_8 ),
    inference(superposition,[],[f272,f47])).

fof(f272,plain,
    ( ! [X0] : r1_tarski(k2_tarski(sK1,sK1),k2_xboole_0(sK2,X0))
    | ~ spl5_8 ),
    inference(resolution,[],[f209,f45])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k2_tarski(sK1,sK1),k2_xboole_0(sK2,X0)) )
    | ~ spl5_8 ),
    inference(superposition,[],[f63,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f226,plain,
    ( spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f219,f198,f223])).

fof(f219,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK2)
    | ~ spl5_7 ),
    inference(superposition,[],[f211,f47])).

fof(f206,plain,
    ( spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f194,f83,f203])).

fof(f194,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f84])).

fof(f84,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f62,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f201,plain,
    ( spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f193,f79,f198])).

fof(f193,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f71,f80])).

fof(f80,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f161,plain,
    ( ~ spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f156,f79,f158])).

fof(f158,plain,
    ( spl5_6
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f156,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f149,f80])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f154,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f153,f140,f75])).

fof(f75,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f153,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f142,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f148,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f145,f75,f83])).

fof(f145,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f133,f47])).

fof(f133,plain,
    ( ! [X0] : r2_hidden(sK1,k2_xboole_0(sK2,X0))
    | ~ spl5_1 ),
    inference(resolution,[],[f125,f67])).

fof(f125,plain,
    ( ! [X0] : r1_tarski(k2_tarski(sK0,sK1),k2_xboole_0(sK2,X0))
    | ~ spl5_1 ),
    inference(resolution,[],[f119,f45])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k2_tarski(sK0,sK1),k2_xboole_0(sK2,X0)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f63,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f143,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f136,f75,f140])).

fof(f136,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f125,f47])).

fof(f96,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f89,f75,f93])).

fof(f93,plain,
    ( spl5_4
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f50,f76])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f88,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f42,f79,f75])).

fof(f42,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f87,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f43,f83,f75])).

fof(f43,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f44,f83,f79,f75])).

fof(f44,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (9280)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (9275)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (9282)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (9281)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (9279)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (9274)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (9272)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (9284)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (9271)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (9270)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (9277)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (9280)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f86,f87,f88,f96,f143,f148,f154,f161,f201,f206,f226,f287,f446,f447,f448,f449,f450,f455])).
% 0.21/0.48  fof(f455,plain,(
% 0.21/0.48    spl5_2 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f453,f140,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl5_2 <=> r2_hidden(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl5_5 <=> r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f142,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(flattening,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f450,plain,(
% 0.21/0.48    spl5_2 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f230,f198,f79])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl5_7 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f216,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(sK2,X0))) ) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f211,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(sK2,X0))) ) | ~spl5_7),
% 0.21/0.48    inference(resolution,[],[f207,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  % (9285)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k2_tarski(sK0,sK0),k2_xboole_0(sK2,X0))) ) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f63,f200])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.48  fof(f449,plain,(
% 0.21/0.48    spl5_2 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f233,f223,f79])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl5_9 <=> r1_tarski(k2_tarski(sK0,sK0),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f225,f67])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    r1_tarski(k2_tarski(sK0,sK0),sK2) | ~spl5_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f448,plain,(
% 0.21/0.48    spl5_2 | ~spl5_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f234,f223,f79])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_9),
% 0.21/0.48    inference(resolution,[],[f225,f66])).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    spl5_2 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f244,f198,f79])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f231,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.48    inference(superposition,[],[f51,f47])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(X0,sK2))) ) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f216,f51])).
% 0.21/0.48  fof(f446,plain,(
% 0.21/0.48    ~spl5_2 | ~spl5_3 | spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f444,f140,f83,f79])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_3 <=> r2_hidden(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl5_5),
% 0.21/0.48    inference(resolution,[],[f68,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl5_10 | ~spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f280,f203,f284])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    spl5_10 <=> r1_tarski(k2_tarski(sK1,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    spl5_8 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    r1_tarski(k2_tarski(sK1,sK1),sK2) | ~spl5_8),
% 0.21/0.48    inference(superposition,[],[f272,f47])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_tarski(sK1,sK1),k2_xboole_0(sK2,X0))) ) | ~spl5_8),
% 0.21/0.48    inference(resolution,[],[f209,f45])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k2_tarski(sK1,sK1),k2_xboole_0(sK2,X0))) ) | ~spl5_8),
% 0.21/0.48    inference(superposition,[],[f63,f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2) | ~spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f203])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl5_9 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f219,f198,f223])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    r1_tarski(k2_tarski(sK0,sK0),sK2) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f211,f47])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl5_8 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f194,f83,f203])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK2) | ~spl5_3),
% 0.21/0.48    inference(resolution,[],[f71,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f62,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl5_7 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f193,f79,f198])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK2) | ~spl5_2),
% 0.21/0.48    inference(resolution,[],[f71,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~spl5_6 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f156,f79,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl5_6 <=> r1_xboole_0(sK2,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~r1_xboole_0(sK2,sK2) | ~spl5_2),
% 0.21/0.48    inference(resolution,[],[f149,f80])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_2),
% 0.21/0.48    inference(resolution,[],[f80,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl5_1 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f153,f140,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f142,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl5_3 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f75,f83])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2) | ~spl5_1),
% 0.21/0.48    inference(superposition,[],[f133,f47])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1,k2_xboole_0(sK2,X0))) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f125,f67])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k2_tarski(sK0,sK1),k2_xboole_0(sK2,X0))) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f119,f45])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k2_tarski(sK0,sK1),k2_xboole_0(sK2,X0))) ) | ~spl5_1),
% 0.21/0.48    inference(superposition,[],[f63,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl5_5 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f136,f75,f140])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 0.21/0.48    inference(superposition,[],[f125,f47])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl5_4 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f89,f75,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl5_4 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r1_xboole_0(k1_xboole_0,sK2) | ~spl5_1),
% 0.21/0.48    inference(superposition,[],[f50,f76])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl5_1 | spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f79,f75])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl5_1 | spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f83,f75])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f83,f79,f75])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9280)------------------------------
% 0.21/0.48  % (9280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9280)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9280)Memory used [KB]: 6396
% 0.21/0.48  % (9280)Time elapsed: 0.071 s
% 0.21/0.48  % (9280)------------------------------
% 0.21/0.48  % (9280)------------------------------
% 0.21/0.48  % (9273)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (9269)Success in time 0.125 s
%------------------------------------------------------------------------------
