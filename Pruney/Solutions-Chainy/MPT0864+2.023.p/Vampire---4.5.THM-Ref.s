%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 170 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  247 ( 663 expanded)
%              Number of equality atoms :  131 ( 363 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f105,f111,f202,f217,f241,f250,f303])).

fof(f303,plain,
    ( spl6_11
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl6_11
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f300,f200])).

fof(f200,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_11
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f300,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f298,f70])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f297,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f297,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_14 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_14 ),
    inference(superposition,[],[f264,f119])).

fof(f119,plain,(
    ! [X1] :
      ( sK5(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f264,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_14 ),
    inference(superposition,[],[f54,f249])).

fof(f249,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl6_14
  <=> sK0 = k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f250,plain,
    ( spl6_14
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f244,f225,f82,f247])).

fof(f82,plain,
    ( spl6_3
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f225,plain,
    ( spl6_13
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f244,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f84,f227])).

fof(f227,plain,
    ( sK0 = sK1
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f225])).

fof(f84,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f241,plain,
    ( spl6_13
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f240,f82,f73,f225])).

fof(f73,plain,
    ( spl6_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f240,plain,
    ( sK0 = sK1
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f229,f75])).

fof(f75,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f229,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl6_3 ),
    inference(superposition,[],[f36,f84])).

fof(f36,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

% (13926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f217,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f209,f86])).

fof(f86,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f60,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f209,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_11 ),
    inference(superposition,[],[f70,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f202,plain,
    ( spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f197,f108,f199])).

fof(f108,plain,
    ( spl6_7
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f197,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f195,f70])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f194,f71])).

fof(f194,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_tarski(X0))
        | k1_tarski(X0) = k1_xboole_0
        | k1_tarski(X0) = k1_xboole_0 )
    | ~ spl6_7 ),
    inference(superposition,[],[f146,f119])).

fof(f146,plain,
    ( ! [X0] :
        ( sK0 != sK5(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(superposition,[],[f55,f110])).

fof(f110,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK5(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f106,f102,f82,f108])).

fof(f102,plain,
    ( spl6_6
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f106,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f84,f104])).

fof(f104,plain,
    ( sK0 = sK2
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( spl6_6
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f100,f82,f77,f102])).

fof(f77,plain,
    ( spl6_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f100,plain,
    ( sK0 = sK2
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f99,f79])).

fof(f79,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f99,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl6_3 ),
    inference(superposition,[],[f37,f84])).

fof(f37,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f80,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f35,f77,f73])).

% (13910)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f35,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:39:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (13913)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (13934)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (13931)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (13916)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13924)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (13912)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (13915)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (13914)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (13932)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (13937)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (13911)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (13931)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f80,f85,f105,f111,f202,f217,f241,f250,f303])).
% 0.21/0.52  fof(f303,plain,(
% 0.21/0.52    spl6_11 | ~spl6_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.52  fof(f302,plain,(
% 0.21/0.52    $false | (spl6_11 | ~spl6_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f300,f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    k1_xboole_0 != k1_tarski(sK0) | spl6_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    spl6_11 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK0) | ~spl6_14),
% 0.21/0.52    inference(resolution,[],[f298,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_14),
% 0.21/0.52    inference(subsumption_resolution,[],[f297,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_14),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f296])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_14),
% 0.21/0.52    inference(superposition,[],[f264,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X1] : (sK5(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.52    inference(resolution,[],[f71,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl6_14),
% 0.21/0.52    inference(superposition,[],[f54,f249])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK0,sK2) | ~spl6_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f247])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl6_14 <=> sK0 = k4_tarski(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl6_14 | ~spl6_3 | ~spl6_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f244,f225,f82,f247])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl6_3 <=> sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    spl6_13 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK0,sK2) | (~spl6_3 | ~spl6_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f84,f227])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl6_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f225])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK2) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    spl6_13 | ~spl6_1 | ~spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f240,f82,f73,f225])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl6_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    sK0 = sK1 | (~spl6_1 | ~spl6_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f229,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    sK0 = k1_mcart_1(sK0) | ~spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    k1_mcart_1(sK0) = sK1 | ~spl6_3),
% 0.21/0.52    inference(superposition,[],[f36,f84])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  % (13926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ~spl6_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    $false | ~spl6_11),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f60,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    r2_hidden(sK0,k1_xboole_0) | ~spl6_11),
% 0.21/0.52    inference(superposition,[],[f70,f201])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK0) | ~spl6_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f199])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    spl6_11 | ~spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f197,f108,f199])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl6_7 <=> sK0 = k4_tarski(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK0) | ~spl6_7),
% 0.21/0.52    inference(resolution,[],[f195,f70])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f194,f71])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_7),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) ) | ~spl6_7),
% 0.21/0.52    inference(superposition,[],[f146,f119])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X0] : (sK0 != sK5(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl6_7),
% 0.21/0.52    inference(superposition,[],[f55,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK0) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK5(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl6_7 | ~spl6_3 | ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f106,f102,f82,f108])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl6_6 <=> sK0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK0) | (~spl6_3 | ~spl6_6)),
% 0.21/0.52    inference(backward_demodulation,[],[f84,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    sK0 = sK2 | ~spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl6_6 | ~spl6_2 | ~spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f82,f77,f102])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl6_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    sK0 = sK2 | (~spl6_2 | ~spl6_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f99,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    sK0 = k2_mcart_1(sK0) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    k2_mcart_1(sK0) = sK2 | ~spl6_3),
% 0.21/0.52    inference(superposition,[],[f37,f84])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f82])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl6_1 | spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f77,f73])).
% 0.21/0.52  % (13910)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (13931)------------------------------
% 0.21/0.52  % (13931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13931)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (13931)Memory used [KB]: 6396
% 0.21/0.52  % (13931)Time elapsed: 0.065 s
% 0.21/0.52  % (13931)------------------------------
% 0.21/0.52  % (13931)------------------------------
% 0.21/0.53  % (13923)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (13908)Success in time 0.169 s
%------------------------------------------------------------------------------
