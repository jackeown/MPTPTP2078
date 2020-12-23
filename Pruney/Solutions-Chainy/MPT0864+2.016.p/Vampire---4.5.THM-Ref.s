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
% DateTime   : Thu Dec  3 12:58:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 295 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  213 ( 918 expanded)
%              Number of equality atoms :  122 ( 587 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f165,f206])).

fof(f206,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f204,f152])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) ),
    inference(subsumption_resolution,[],[f150,f76])).

fof(f76,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f150,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(superposition,[],[f72,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f66,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f204,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f203,f76])).

fof(f203,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f193,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_1 ),
    inference(extensionality_resolution,[],[f77,f175])).

fof(f175,plain,
    ( ! [X1] :
        ( sK1 != sK4(X1)
        | ~ r2_hidden(sK1,X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_1 ),
    inference(superposition,[],[f41,f171])).

fof(f171,plain,
    ( sK1 = k4_tarski(sK1,sK3)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f35,f167])).

fof(f167,plain,
    ( sK1 = sK2
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f95,f85])).

fof(f85,plain,
    ( sK1 = k1_mcart_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_1
  <=> sK1 = k1_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f95,plain,(
    k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f35,plain,(
    sK1 = k4_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & sK1 = k4_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK1
   => sK1 = k4_tarski(sK2,sK3) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl7_2 ),
    inference(resolution,[],[f151,f142])).

fof(f142,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl7_2 ),
    inference(superposition,[],[f76,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f136,f76])).

fof(f136,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f118,f40])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(extensionality_resolution,[],[f77,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( sK1 != sK4(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_2 ),
    inference(superposition,[],[f42,f98])).

fof(f98,plain,
    ( sK1 = k4_tarski(sK2,sK1)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f35,f97])).

fof(f97,plain,
    ( sK1 = sK3
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f96,f89])).

fof(f89,plain,
    ( sK1 = k2_mcart_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_2
  <=> sK1 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f96,plain,(
    k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[],[f46,f35])).

fof(f46,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f151,plain,
    ( ! [X0] : ~ r2_hidden(sK1,X0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,
    ( ! [X0] :
        ( k4_xboole_0(X0,k1_xboole_0) != X0
        | ~ r2_hidden(sK1,X0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f72,f137])).

fof(f90,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f36,f87,f83])).

fof(f36,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (30430)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (30430)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f90,f165,f206])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~spl7_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    $false | ~spl7_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f204,f152])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f150,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.46    inference(equality_resolution,[],[f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.21/0.46    inference(equality_resolution,[],[f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.46    inference(definition_unfolding,[],[f48,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f39,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f43,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(rectify,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k2_enumset1(X0,X0,X0,X0) | ~r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.21/0.46    inference(superposition,[],[f72,f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(forward_demodulation,[],[f66,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f37,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f51,f65])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f203,f76])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_1),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f201])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_1),
% 0.21/0.46    inference(resolution,[],[f193,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(sK4(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl7_1),
% 0.21/0.46    inference(extensionality_resolution,[],[f77,f175])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    ( ! [X1] : (sK1 != sK4(X1) | ~r2_hidden(sK1,X1) | k1_xboole_0 = X1) ) | ~spl7_1),
% 0.21/0.46    inference(superposition,[],[f41,f171])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    sK1 = k4_tarski(sK1,sK3) | ~spl7_1),
% 0.21/0.46    inference(forward_demodulation,[],[f35,f167])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    sK1 = sK2 | ~spl7_1),
% 0.21/0.47    inference(backward_demodulation,[],[f95,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    sK1 = k1_mcart_1(sK1) | ~spl7_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl7_1 <=> sK1 = k1_mcart_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    k1_mcart_1(sK1) = sK2),
% 0.21/0.47    inference(superposition,[],[f45,f35])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X2,X1] : k4_tarski(X1,X2) = sK1 => sK1 = k4_tarski(sK2,sK3)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.47    inference(equality_resolution,[],[f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.47    inference(definition_unfolding,[],[f47,f65])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ~spl7_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    $false | ~spl7_2),
% 0.21/0.47    inference(resolution,[],[f151,f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    r2_hidden(sK1,k1_xboole_0) | ~spl7_2),
% 0.21/0.47    inference(superposition,[],[f76,f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f76])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_2),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl7_2),
% 0.21/0.47    inference(resolution,[],[f118,f40])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK4(X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl7_2),
% 0.21/0.47    inference(extensionality_resolution,[],[f77,f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (sK1 != sK4(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl7_2),
% 0.21/0.47    inference(superposition,[],[f42,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    sK1 = k4_tarski(sK2,sK1) | ~spl7_2),
% 0.21/0.47    inference(backward_demodulation,[],[f35,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    sK1 = sK3 | ~spl7_2),
% 0.21/0.47    inference(forward_demodulation,[],[f96,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    sK1 = k2_mcart_1(sK1) | ~spl7_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl7_2 <=> sK1 = k2_mcart_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    k2_mcart_1(sK1) = sK3),
% 0.21/0.47    inference(superposition,[],[f46,f35])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK1,X0)) ) | ~spl7_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f38])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) != X0 | ~r2_hidden(sK1,X0)) ) | ~spl7_2),
% 0.21/0.47    inference(superposition,[],[f72,f137])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl7_1 | spl7_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f87,f83])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30430)------------------------------
% 0.21/0.47  % (30430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30430)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30430)Memory used [KB]: 10746
% 0.21/0.47  % (30430)Time elapsed: 0.085 s
% 0.21/0.47  % (30430)------------------------------
% 0.21/0.47  % (30430)------------------------------
% 0.21/0.47  % (30423)Success in time 0.117 s
%------------------------------------------------------------------------------
