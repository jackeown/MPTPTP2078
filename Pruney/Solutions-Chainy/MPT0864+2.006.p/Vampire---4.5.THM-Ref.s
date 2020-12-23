%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 213 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  242 ( 811 expanded)
%              Number of equality atoms :  130 ( 480 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f172,f249])).

fof(f249,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f247,f116])).

fof(f116,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f84,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_mcart_1(X0))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f247,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f56,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f233,f56])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f232,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f30])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f232,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_1 ),
    inference(superposition,[],[f216,f79])).

fof(f79,plain,(
    ! [X1] :
      ( sK3(k2_tarski(X1,X1)) = X1
      | k1_xboole_0 = k2_tarski(X1,X1) ) ),
    inference(resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f216,plain,
    ( ! [X1] :
        ( sK0 != sK3(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_1 ),
    inference(superposition,[],[f32,f199])).

fof(f199,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f28,f179])).

fof(f179,plain,
    ( sK0 = sK1
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f70,f63])).

fof(f63,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f28,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f30])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f172,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f168,f116])).

fof(f168,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f56,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f162,f56])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f161,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k2_tarski(X0,X0))
        | k2_tarski(X0,X0) = k1_xboole_0
        | k2_tarski(X0,X0) = k1_xboole_0 )
    | ~ spl5_2 ),
    inference(superposition,[],[f132,f79])).

% (14138)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f132,plain,
    ( ! [X0] :
        ( sK0 != sK3(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(superposition,[],[f33,f73])).

fof(f73,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f28,f72])).

fof(f72,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f71,f67])).

fof(f67,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

% (14138)Refutation not found, incomplete strategy% (14138)------------------------------
% (14138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f65,plain,
    ( spl5_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f35,f28])).

fof(f35,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f65,f61])).

fof(f29,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:39:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (14130)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (14128)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.53  % (14124)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (14147)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.53  % (14132)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.53  % (14130)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (14129)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.25/0.54  % (14139)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.25/0.54  % (14125)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.54  % (14125)Refutation not found, incomplete strategy% (14125)------------------------------
% 1.25/0.54  % (14125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (14125)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (14125)Memory used [KB]: 1663
% 1.25/0.54  % (14125)Time elapsed: 0.125 s
% 1.25/0.54  % (14125)------------------------------
% 1.25/0.54  % (14125)------------------------------
% 1.40/0.54  % (14136)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.54  % (14141)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.54  % (14136)Refutation not found, incomplete strategy% (14136)------------------------------
% 1.40/0.54  % (14136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14136)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14136)Memory used [KB]: 10618
% 1.40/0.54  % (14136)Time elapsed: 0.136 s
% 1.40/0.54  % (14136)------------------------------
% 1.40/0.54  % (14136)------------------------------
% 1.40/0.54  % (14141)Refutation not found, incomplete strategy% (14141)------------------------------
% 1.40/0.54  % (14141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14141)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14141)Memory used [KB]: 1663
% 1.40/0.54  % (14141)Time elapsed: 0.134 s
% 1.40/0.54  % (14141)------------------------------
% 1.40/0.54  % (14141)------------------------------
% 1.40/0.54  % (14144)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (14126)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.55  % (14146)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.55  % (14140)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.55  % (14134)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.55  % (14153)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.55  % (14148)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.55  % (14153)Refutation not found, incomplete strategy% (14153)------------------------------
% 1.40/0.55  % (14153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14153)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14153)Memory used [KB]: 1663
% 1.40/0.55  % (14153)Time elapsed: 0.001 s
% 1.40/0.55  % (14153)------------------------------
% 1.40/0.55  % (14153)------------------------------
% 1.40/0.55  % (14133)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.55  % (14134)Refutation not found, incomplete strategy% (14134)------------------------------
% 1.40/0.55  % (14134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14134)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14134)Memory used [KB]: 10746
% 1.40/0.55  % (14134)Time elapsed: 0.134 s
% 1.40/0.55  % (14134)------------------------------
% 1.40/0.55  % (14134)------------------------------
% 1.40/0.55  % (14143)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (14140)Refutation not found, incomplete strategy% (14140)------------------------------
% 1.40/0.55  % (14140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14127)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.55  % (14140)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14140)Memory used [KB]: 10618
% 1.40/0.55  % (14140)Time elapsed: 0.148 s
% 1.40/0.55  % (14140)------------------------------
% 1.40/0.55  % (14140)------------------------------
% 1.40/0.55  % (14149)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (14145)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f250,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f68,f172,f249])).
% 1.40/0.55  fof(f249,plain,(
% 1.40/0.55    ~spl5_1),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f248])).
% 1.40/0.55  fof(f248,plain,(
% 1.40/0.55    $false | ~spl5_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f247,f116])).
% 1.40/0.55  fof(f116,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.40/0.55    inference(resolution,[],[f84,f53])).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f84,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X1,k1_mcart_1(X0)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.40/0.55    inference(resolution,[],[f82,f46])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,plain,(
% 1.40/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.40/0.55  fof(f82,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.40/0.55    inference(superposition,[],[f47,f58])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.40/0.55    inference(equality_resolution,[],[f45])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.40/0.55    inference(flattening,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.40/0.55    inference(nnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.40/0.55  fof(f247,plain,(
% 1.40/0.55    r2_hidden(sK0,k1_xboole_0) | ~spl5_1),
% 1.40/0.55    inference(superposition,[],[f56,f234])).
% 1.40/0.55  fof(f234,plain,(
% 1.40/0.55    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl5_1),
% 1.40/0.55    inference(resolution,[],[f233,f56])).
% 1.40/0.55  fof(f233,plain,(
% 1.40/0.55    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f232,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.40/0.55    inference(equality_resolution,[],[f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.40/0.55    inference(definition_unfolding,[],[f39,f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.55    inference(rectify,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.40/0.55  fof(f232,plain,(
% 1.40/0.55    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_1),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f231])).
% 1.40/0.55  fof(f231,plain,(
% 1.40/0.55    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_1),
% 1.40/0.55    inference(superposition,[],[f216,f79])).
% 1.40/0.55  fof(f79,plain,(
% 1.40/0.55    ( ! [X1] : (sK3(k2_tarski(X1,X1)) = X1 | k1_xboole_0 = k2_tarski(X1,X1)) )),
% 1.40/0.55    inference(resolution,[],[f57,f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f12,plain,(
% 1.40/0.55    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.40/0.55    inference(ennf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.40/0.55  fof(f216,plain,(
% 1.40/0.55    ( ! [X1] : (sK0 != sK3(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl5_1),
% 1.40/0.55    inference(superposition,[],[f32,f199])).
% 1.40/0.55  fof(f199,plain,(
% 1.40/0.55    sK0 = k4_tarski(sK0,sK2) | ~spl5_1),
% 1.40/0.55    inference(forward_demodulation,[],[f28,f179])).
% 1.40/0.55  fof(f179,plain,(
% 1.40/0.55    sK0 = sK1 | ~spl5_1),
% 1.40/0.55    inference(backward_demodulation,[],[f70,f63])).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    sK0 = k1_mcart_1(sK0) | ~spl5_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f61])).
% 1.40/0.56  fof(f61,plain,(
% 1.40/0.56    spl5_1 <=> sK0 = k1_mcart_1(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.40/0.56  fof(f70,plain,(
% 1.40/0.56    k1_mcart_1(sK0) = sK1),
% 1.40/0.56    inference(superposition,[],[f34,f28])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f7])).
% 1.40/0.56  fof(f7,axiom,(
% 1.40/0.56    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    sK0 = k4_tarski(sK1,sK2)),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  fof(f17,plain,(
% 1.40/0.56    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.40/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16,f15])).
% 1.40/0.56  fof(f15,plain,(
% 1.40/0.56    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f11,plain,(
% 1.40/0.56    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.40/0.56    inference(ennf_transformation,[],[f10])).
% 1.40/0.56  fof(f10,negated_conjecture,(
% 1.40/0.56    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.40/0.56    inference(negated_conjecture,[],[f9])).
% 1.40/0.56  fof(f9,conjecture,(
% 1.40/0.56    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f19])).
% 1.40/0.56  fof(f56,plain,(
% 1.40/0.56    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.40/0.56    inference(equality_resolution,[],[f55])).
% 1.40/0.56  fof(f55,plain,(
% 1.40/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.40/0.56    inference(equality_resolution,[],[f51])).
% 1.40/0.56  fof(f51,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.40/0.56    inference(definition_unfolding,[],[f40,f30])).
% 1.40/0.56  fof(f40,plain,(
% 1.40/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f172,plain,(
% 1.40/0.56    ~spl5_2),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f171])).
% 1.40/0.56  fof(f171,plain,(
% 1.40/0.56    $false | ~spl5_2),
% 1.40/0.56    inference(subsumption_resolution,[],[f168,f116])).
% 1.40/0.56  fof(f168,plain,(
% 1.40/0.56    r2_hidden(sK0,k1_xboole_0) | ~spl5_2),
% 1.40/0.56    inference(superposition,[],[f56,f163])).
% 1.40/0.56  fof(f163,plain,(
% 1.40/0.56    k1_xboole_0 = k2_tarski(sK0,sK0) | ~spl5_2),
% 1.40/0.56    inference(resolution,[],[f162,f56])).
% 1.40/0.56  fof(f162,plain,(
% 1.40/0.56    ( ! [X0] : (~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_2),
% 1.40/0.56    inference(subsumption_resolution,[],[f161,f57])).
% 1.40/0.56  fof(f161,plain,(
% 1.40/0.56    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_2),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f150])).
% 1.40/0.56  fof(f150,plain,(
% 1.40/0.56    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k2_tarski(X0,X0)) | k2_tarski(X0,X0) = k1_xboole_0 | k2_tarski(X0,X0) = k1_xboole_0) ) | ~spl5_2),
% 1.40/0.56    inference(superposition,[],[f132,f79])).
% 1.40/0.56  % (14138)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.56  fof(f132,plain,(
% 1.40/0.56    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl5_2),
% 1.40/0.56    inference(superposition,[],[f33,f73])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    sK0 = k4_tarski(sK1,sK0) | ~spl5_2),
% 1.40/0.56    inference(backward_demodulation,[],[f28,f72])).
% 1.40/0.56  fof(f72,plain,(
% 1.40/0.56    sK0 = sK2 | ~spl5_2),
% 1.40/0.56    inference(forward_demodulation,[],[f71,f67])).
% 1.40/0.56  fof(f67,plain,(
% 1.40/0.56    sK0 = k2_mcart_1(sK0) | ~spl5_2),
% 1.40/0.56    inference(avatar_component_clause,[],[f65])).
% 1.40/0.56  % (14138)Refutation not found, incomplete strategy% (14138)------------------------------
% 1.40/0.56  % (14138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    spl5_2 <=> sK0 = k2_mcart_1(sK0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.40/0.56  fof(f71,plain,(
% 1.40/0.56    k2_mcart_1(sK0) = sK2),
% 1.40/0.56    inference(superposition,[],[f35,f28])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f7])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.40/0.56    inference(cnf_transformation,[],[f19])).
% 1.40/0.56  fof(f68,plain,(
% 1.40/0.56    spl5_1 | spl5_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f29,f65,f61])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (14130)------------------------------
% 1.40/0.56  % (14130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (14130)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (14130)Memory used [KB]: 10746
% 1.40/0.56  % (14130)Time elapsed: 0.124 s
% 1.40/0.56  % (14130)------------------------------
% 1.40/0.56  % (14130)------------------------------
% 1.40/0.56  % (14137)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.56  % (14123)Success in time 0.194 s
%------------------------------------------------------------------------------
