%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 207 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  344 ( 725 expanded)
%              Number of equality atoms :  306 ( 663 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f237,f270])).

fof(f270,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f25,f236])).

fof(f236,plain,
    ( ! [X1] : sK1 = X1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_3
  <=> ! [X1] : sK1 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f237,plain,
    ( spl4_3
    | spl4_3 ),
    inference(avatar_split_clause,[],[f233,f235,f235])).

fof(f233,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1 ) ),
    inference(global_subsumption,[],[f25,f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( sK0 = sK1
      | sK1 = X0
      | sK1 = X1 ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK0 = sK1
      | sK1 = X0
      | sK1 = X1
      | sK0 = sK1 ) ),
    inference(resolution,[],[f131,f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] :
      ( ~ r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | X8 = X11 ) ),
    inference(equality_resolution,[],[f86])).

% (19576)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f36,f57,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( X8 = X11
      | X7 = X11
      | X6 = X11
      | X5 = X11
      | X4 = X11
      | X3 = X11
      | X2 = X11
      | X1 = X11
      | X0 = X11
      | ~ r2_hidden(X11,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f23])).

% (19584)Termination reason: Refutation not found, incomplete strategy

% (19584)Memory used [KB]: 10746
% (19584)Time elapsed: 0.119 s
% (19584)------------------------------
% (19584)------------------------------
fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X10] :
          ( ( ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 )
            | ~ r2_hidden(X10,X9) )
          & ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10
            | r2_hidden(X10,X9) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X9)
              | ( X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
        | ? [X10] :
            ( ( ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 )
              | ~ r2_hidden(X10,X9) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | r2_hidden(X10,X9) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X9)
              | ( X8 != X10
                & X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X8 = X10
              | X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X9) ) )
        | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f131,plain,(
    ! [X4,X3] : r2_hidden(sK1,k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k5_xboole_0(k6_enumset1(X3,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(X3,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4))))) ),
    inference(superposition,[],[f90,f118])).

fof(f118,plain,(
    ! [X0] : k6_enumset1(X0,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(X0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f106,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f35,f57,f63,f34])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f106,plain,(
    ! [X0] : k6_enumset1(X0,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(superposition,[],[f65,f66])).

fof(f66,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(definition_unfolding,[],[f24,f63,f62])).

fof(f24,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1,X11] : r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X7 != X11
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9 ) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] :
      ( r2_hidden(X11,X9)
      | X7 != X11
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:57:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (19574)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.49  % (19574)Refutation not found, incomplete strategy% (19574)------------------------------
% 0.20/0.49  % (19574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19574)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (19574)Memory used [KB]: 10618
% 0.20/0.49  % (19574)Time elapsed: 0.103 s
% 0.20/0.49  % (19574)------------------------------
% 0.20/0.49  % (19574)------------------------------
% 0.20/0.49  % (19565)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (19567)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (19580)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (19589)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (19568)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (19571)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (19584)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (19582)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (19584)Refutation not found, incomplete strategy% (19584)------------------------------
% 0.20/0.51  % (19584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19565)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f237,f270])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    ~spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    $false | ~spl4_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f25,f236])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ( ! [X1] : (sK1 = X1) ) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f235])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    spl4_3 <=> ! [X1] : sK1 = X1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK0 != sK1 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (X0 != X1 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    spl4_3 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f233,f235,f235])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1) )),
% 0.20/0.51    inference(global_subsumption,[],[f25,f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK0 = sK1 | sK1 = X0 | sK1 = X1) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f229])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK1 = X0 | sK1 = X1 | sK0 = sK1) )),
% 0.20/0.51    inference(resolution,[],[f131,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11] : (~r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | X8 = X11) )),
% 0.20/0.51    inference(equality_resolution,[],[f86])).
% 0.20/0.51  % (19576)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 0.20/0.52    inference(definition_unfolding,[],[f37,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f36,f57,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f26,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f27,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f31,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  % (19584)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19584)Memory used [KB]: 10746
% 0.20/0.52  % (19584)Time elapsed: 0.119 s
% 0.20/0.52  % (19584)------------------------------
% 0.20/0.52  % (19584)------------------------------
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X8 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X7 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X8 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X7 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9),X9))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X11] : ((r2_hidden(X11,X9) | (X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.20/0.52    inference(rectify,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : ((k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 | ? [X10] : (((X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10) | ~r2_hidden(X10,X9)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | r2_hidden(X10,X9)))) & (! [X10] : ((r2_hidden(X10,X9) | (X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & ((X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10) | ~r2_hidden(X10,X9))) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9))),
% 0.20/0.52    inference(nnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X4,X3] : (r2_hidden(sK1,k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k5_xboole_0(k6_enumset1(X3,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(X3,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4)))))) )),
% 0.20/0.52    inference(superposition,[],[f90,f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X0] : (k6_enumset1(X0,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(X0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f106,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f57,f63,f34])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (k6_enumset1(X0,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 0.20/0.52    inference(superposition,[],[f65,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 0.20/0.52    inference(definition_unfolding,[],[f24,f63,f62])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X5,X3,X1,X11] : (r2_hidden(X11,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))))) )),
% 0.20/0.52    inference(equality_resolution,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X11,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 0.20/0.52    inference(equality_resolution,[],[f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X7 != X11 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k3_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != X9) )),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f64])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X11,X9] : (r2_hidden(X11,X9) | X7 != X11 | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (19565)------------------------------
% 0.20/0.52  % (19565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19565)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (19565)Memory used [KB]: 11001
% 0.20/0.52  % (19565)Time elapsed: 0.120 s
% 0.20/0.52  % (19565)------------------------------
% 0.20/0.52  % (19565)------------------------------
% 0.20/0.52  % (19577)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (19578)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (19587)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (19587)Refutation not found, incomplete strategy% (19587)------------------------------
% 0.20/0.52  % (19587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19587)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19587)Memory used [KB]: 1791
% 0.20/0.52  % (19587)Time elapsed: 0.120 s
% 0.20/0.52  % (19587)------------------------------
% 0.20/0.52  % (19587)------------------------------
% 0.20/0.52  % (19592)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (19564)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19569)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (19563)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (19572)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (19586)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (19562)Success in time 0.181 s
%------------------------------------------------------------------------------
