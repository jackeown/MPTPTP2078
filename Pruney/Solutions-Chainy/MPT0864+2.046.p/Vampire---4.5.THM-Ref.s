%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:37 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 169 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 ( 637 expanded)
%              Number of equality atoms :  138 ( 396 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f65,f72,f78,f153,f169,f175,f195])).

fof(f195,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f81,f82,f95,f184])).

fof(f184,plain,
    ( ! [X1] :
        ( sK0 != sK4(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl5_10 ),
    inference(superposition,[],[f36,f174])).

fof(f174,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_10
  <=> sK0 = k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
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

fof(f95,plain,(
    ! [X1] : sK4(k1_tarski(X1)) = X1 ),
    inference(subsumption_resolution,[],[f93,f81])).

fof(f93,plain,(
    ! [X1] :
      ( sK4(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f88,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f45,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f82,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f44,f38])).

fof(f44,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f175,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f170,f166,f56,f172])).

fof(f56,plain,
    ( spl5_3
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f166,plain,
    ( spl5_9
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f170,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f58,f168])).

fof(f168,plain,
    ( sK0 = sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f58,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f169,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f164,f62,f47,f166])).

fof(f47,plain,
    ( spl5_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f62,plain,
    ( spl5_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( sK0 = sK1
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f64,f49])).

fof(f49,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f64,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f153,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f81,f82,f95,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( sK0 != sK4(X0)
        | ~ r2_hidden(sK0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_6 ),
    inference(superposition,[],[f37,f77])).

fof(f77,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,
    ( spl5_6
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f73,f69,f56,f75])).

fof(f69,plain,
    ( spl5_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f73,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f58,f71])).

fof(f71,plain,
    ( sK0 = sK2
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,
    ( spl5_5
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f67,f56,f51,f69])).

fof(f51,plain,
    ( spl5_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f67,plain,
    ( sK0 = sK2
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f66,f53])).

fof(f53,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f66,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl5_3 ),
    inference(superposition,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f65,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f60,f56,f62])).

fof(f60,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl5_3 ),
    inference(superposition,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
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

fof(f54,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f24,f51,f47])).

fof(f24,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (8447)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8450)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (8463)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (8448)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (8463)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f198,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(avatar_sat_refutation,[],[f54,f59,f65,f72,f78,f153,f169,f175,f195])).
% 1.27/0.53  fof(f195,plain,(
% 1.27/0.53    ~spl5_10),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f191])).
% 1.27/0.53  fof(f191,plain,(
% 1.27/0.53    $false | ~spl5_10),
% 1.27/0.53    inference(unit_resulting_resolution,[],[f81,f82,f95,f184])).
% 1.27/0.53  fof(f184,plain,(
% 1.27/0.53    ( ! [X1] : (sK0 != sK4(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl5_10),
% 1.27/0.53    inference(superposition,[],[f36,f174])).
% 1.27/0.53  fof(f174,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK0,sK2) | ~spl5_10),
% 1.27/0.53    inference(avatar_component_clause,[],[f172])).
% 1.27/0.53  fof(f172,plain,(
% 1.27/0.53    spl5_10 <=> sK0 = k4_tarski(sK0,sK2)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.27/0.53  fof(f36,plain,(
% 1.27/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f22])).
% 1.27/0.53  fof(f22,plain,(
% 1.27/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f12,plain,(
% 1.27/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.27/0.53    inference(ennf_transformation,[],[f8])).
% 1.27/0.53  fof(f8,axiom,(
% 1.27/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.27/0.53  fof(f95,plain,(
% 1.27/0.53    ( ! [X1] : (sK4(k1_tarski(X1)) = X1) )),
% 1.27/0.53    inference(subsumption_resolution,[],[f93,f81])).
% 1.27/0.53  fof(f93,plain,(
% 1.27/0.53    ( ! [X1] : (sK4(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 1.27/0.53    inference(resolution,[],[f88,f35])).
% 1.27/0.53  fof(f35,plain,(
% 1.27/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f22])).
% 1.27/0.53  fof(f88,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 1.27/0.53    inference(duplicate_literal_removal,[],[f87])).
% 1.27/0.53  fof(f87,plain,(
% 1.27/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 1.27/0.53    inference(superposition,[],[f45,f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.53  fof(f45,plain,(
% 1.27/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.27/0.53    inference(equality_resolution,[],[f27])).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.27/0.53    inference(cnf_transformation,[],[f20])).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(rectify,[],[f17])).
% 1.27/0.53  fof(f17,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(flattening,[],[f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(nnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.27/0.53  fof(f82,plain,(
% 1.27/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.27/0.53    inference(superposition,[],[f44,f38])).
% 1.27/0.53  fof(f44,plain,(
% 1.27/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.27/0.53    inference(equality_resolution,[],[f43])).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.27/0.53    inference(equality_resolution,[],[f28])).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.27/0.53    inference(cnf_transformation,[],[f20])).
% 1.27/0.53  fof(f81,plain,(
% 1.27/0.53    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.27/0.53    inference(superposition,[],[f34,f39])).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f6])).
% 1.27/0.53  fof(f6,axiom,(
% 1.27/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.27/0.53  fof(f175,plain,(
% 1.27/0.53    spl5_10 | ~spl5_3 | ~spl5_9),
% 1.27/0.53    inference(avatar_split_clause,[],[f170,f166,f56,f172])).
% 1.27/0.53  fof(f56,plain,(
% 1.27/0.53    spl5_3 <=> sK0 = k4_tarski(sK1,sK2)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.27/0.53  fof(f166,plain,(
% 1.27/0.53    spl5_9 <=> sK0 = sK1),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.27/0.53  fof(f170,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK0,sK2) | (~spl5_3 | ~spl5_9)),
% 1.27/0.53    inference(forward_demodulation,[],[f58,f168])).
% 1.27/0.53  fof(f168,plain,(
% 1.27/0.53    sK0 = sK1 | ~spl5_9),
% 1.27/0.53    inference(avatar_component_clause,[],[f166])).
% 1.27/0.53  fof(f58,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK1,sK2) | ~spl5_3),
% 1.27/0.53    inference(avatar_component_clause,[],[f56])).
% 1.27/0.53  fof(f169,plain,(
% 1.27/0.53    spl5_9 | ~spl5_1 | ~spl5_4),
% 1.27/0.53    inference(avatar_split_clause,[],[f164,f62,f47,f166])).
% 1.27/0.53  fof(f47,plain,(
% 1.27/0.53    spl5_1 <=> sK0 = k1_mcart_1(sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.27/0.53  fof(f62,plain,(
% 1.27/0.53    spl5_4 <=> k1_mcart_1(sK0) = sK1),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.27/0.53  fof(f164,plain,(
% 1.27/0.53    sK0 = sK1 | (~spl5_1 | ~spl5_4)),
% 1.27/0.53    inference(backward_demodulation,[],[f64,f49])).
% 1.27/0.53  fof(f49,plain,(
% 1.27/0.53    sK0 = k1_mcart_1(sK0) | ~spl5_1),
% 1.27/0.53    inference(avatar_component_clause,[],[f47])).
% 1.27/0.53  fof(f64,plain,(
% 1.27/0.53    k1_mcart_1(sK0) = sK1 | ~spl5_4),
% 1.27/0.53    inference(avatar_component_clause,[],[f62])).
% 1.27/0.53  fof(f153,plain,(
% 1.27/0.53    ~spl5_6),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f147])).
% 1.27/0.53  fof(f147,plain,(
% 1.27/0.53    $false | ~spl5_6),
% 1.27/0.53    inference(unit_resulting_resolution,[],[f81,f82,f95,f90])).
% 1.27/0.53  fof(f90,plain,(
% 1.27/0.53    ( ! [X0] : (sK0 != sK4(X0) | ~r2_hidden(sK0,X0) | k1_xboole_0 = X0) ) | ~spl5_6),
% 1.27/0.53    inference(superposition,[],[f37,f77])).
% 1.27/0.53  fof(f77,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK1,sK0) | ~spl5_6),
% 1.27/0.53    inference(avatar_component_clause,[],[f75])).
% 1.27/0.53  fof(f75,plain,(
% 1.27/0.53    spl5_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.27/0.53  fof(f37,plain,(
% 1.27/0.53    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f22])).
% 1.27/0.53  fof(f78,plain,(
% 1.27/0.53    spl5_6 | ~spl5_3 | ~spl5_5),
% 1.27/0.53    inference(avatar_split_clause,[],[f73,f69,f56,f75])).
% 1.27/0.53  fof(f69,plain,(
% 1.27/0.53    spl5_5 <=> sK0 = sK2),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.27/0.53  fof(f73,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK1,sK0) | (~spl5_3 | ~spl5_5)),
% 1.27/0.53    inference(backward_demodulation,[],[f58,f71])).
% 1.27/0.53  fof(f71,plain,(
% 1.27/0.53    sK0 = sK2 | ~spl5_5),
% 1.27/0.53    inference(avatar_component_clause,[],[f69])).
% 1.27/0.53  fof(f72,plain,(
% 1.27/0.53    spl5_5 | ~spl5_2 | ~spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f67,f56,f51,f69])).
% 1.27/0.53  fof(f51,plain,(
% 1.27/0.53    spl5_2 <=> sK0 = k2_mcart_1(sK0)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.27/0.53  fof(f67,plain,(
% 1.27/0.53    sK0 = sK2 | (~spl5_2 | ~spl5_3)),
% 1.27/0.53    inference(forward_demodulation,[],[f66,f53])).
% 1.27/0.53  fof(f53,plain,(
% 1.27/0.53    sK0 = k2_mcart_1(sK0) | ~spl5_2),
% 1.27/0.53    inference(avatar_component_clause,[],[f51])).
% 1.27/0.53  fof(f66,plain,(
% 1.27/0.53    k2_mcart_1(sK0) = sK2 | ~spl5_3),
% 1.27/0.53    inference(superposition,[],[f26,f58])).
% 1.27/0.53  fof(f26,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.27/0.53    inference(cnf_transformation,[],[f7])).
% 1.27/0.53  fof(f7,axiom,(
% 1.27/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.27/0.53  fof(f65,plain,(
% 1.27/0.53    spl5_4 | ~spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f60,f56,f62])).
% 1.27/0.53  fof(f60,plain,(
% 1.27/0.53    k1_mcart_1(sK0) = sK1 | ~spl5_3),
% 1.27/0.53    inference(superposition,[],[f25,f58])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.27/0.53    inference(cnf_transformation,[],[f7])).
% 1.27/0.53  fof(f59,plain,(
% 1.27/0.53    spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f23,f56])).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    sK0 = k4_tarski(sK1,sK2)),
% 1.27/0.53    inference(cnf_transformation,[],[f15])).
% 1.27/0.53  fof(f15,plain,(
% 1.27/0.53    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13])).
% 1.27/0.53  fof(f13,plain,(
% 1.27/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f14,plain,(
% 1.27/0.53    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f11,plain,(
% 1.27/0.53    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.27/0.53    inference(ennf_transformation,[],[f10])).
% 1.27/0.53  fof(f10,negated_conjecture,(
% 1.27/0.53    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.27/0.53    inference(negated_conjecture,[],[f9])).
% 1.27/0.53  fof(f9,conjecture,(
% 1.27/0.53    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.27/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.27/0.53  fof(f54,plain,(
% 1.27/0.53    spl5_1 | spl5_2),
% 1.27/0.53    inference(avatar_split_clause,[],[f24,f51,f47])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.27/0.53    inference(cnf_transformation,[],[f15])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (8463)------------------------------
% 1.27/0.53  % (8463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (8463)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (8463)Memory used [KB]: 6268
% 1.27/0.53  % (8463)Time elapsed: 0.117 s
% 1.27/0.53  % (8463)------------------------------
% 1.27/0.53  % (8463)------------------------------
% 1.27/0.54  % (8441)Success in time 0.172 s
%------------------------------------------------------------------------------
