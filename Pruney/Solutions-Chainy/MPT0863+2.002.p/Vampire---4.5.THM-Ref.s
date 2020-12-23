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
% DateTime   : Thu Dec  3 12:58:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 180 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 (1005 expanded)
%              Number of equality atoms :   99 ( 491 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f329,f293])).

fof(f293,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f290,f32])).

fof(f32,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( sK4 != k2_mcart_1(sK0)
          & sK3 != k2_mcart_1(sK0) )
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f290,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f282])).

fof(f282,plain,
    ( sK4 != sK4
    | sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f34,f267])).

fof(f267,plain,
    ( sK4 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f256,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f256,plain,
    ( r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))
    | sK4 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,
    ( r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0)))
    | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) ),
    inference(resolution,[],[f162,f63])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f162,plain,(
    ! [X7] :
      ( ~ r2_hidden(k2_mcart_1(sK0),X7)
      | r2_hidden(sK4,X7)
      | r2_hidden(sK3,X7) ) ),
    inference(resolution,[],[f122,f78])).

fof(f78,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f122,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_hidden(X17,k2_tarski(X14,X15))
      | ~ r2_hidden(X17,X16)
      | r2_hidden(X15,X16)
      | r2_hidden(X14,X16) ) ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f34,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f329,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f328])).

fof(f328,plain,
    ( sK2 != sK2
    | sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f294,f212])).

fof(f212,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f203,f64])).

fof(f203,plain,
    ( r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))
    | sK2 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f176,f64])).

fof(f176,plain,
    ( r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0)))
    | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,(
    ! [X6] :
      ( ~ r2_hidden(k1_mcart_1(sK0),X6)
      | r2_hidden(sK2,X6)
      | r2_hidden(sK1,X6) ) ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f294,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f289,f33])).

fof(f33,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f289,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( sK4 != sK4
    | sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f35,f267])).

fof(f35,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:51:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (5845)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.49  % (5858)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.50  % (5850)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.50  % (5853)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (5858)Refutation not found, incomplete strategy% (5858)------------------------------
% 0.22/0.50  % (5858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5858)Memory used [KB]: 10746
% 0.22/0.50  % (5858)Time elapsed: 0.078 s
% 0.22/0.50  % (5858)------------------------------
% 0.22/0.50  % (5858)------------------------------
% 0.22/0.50  % (5842)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (5837)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (5842)Refutation not found, incomplete strategy% (5842)------------------------------
% 0.22/0.51  % (5842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5842)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (5842)Memory used [KB]: 10618
% 0.22/0.51  % (5842)Time elapsed: 0.087 s
% 0.22/0.51  % (5842)------------------------------
% 0.22/0.51  % (5842)------------------------------
% 0.22/0.51  % (5834)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (5831)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (5840)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (5848)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (5832)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (5839)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (5844)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (5841)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (5847)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (5844)Refutation not found, incomplete strategy% (5844)------------------------------
% 0.22/0.53  % (5844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5840)Refutation not found, incomplete strategy% (5840)------------------------------
% 0.22/0.53  % (5840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5848)Refutation not found, incomplete strategy% (5848)------------------------------
% 0.22/0.53  % (5848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5848)Memory used [KB]: 1663
% 0.22/0.53  % (5848)Time elapsed: 0.121 s
% 0.22/0.53  % (5848)------------------------------
% 0.22/0.53  % (5848)------------------------------
% 0.22/0.53  % (5840)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5840)Memory used [KB]: 10746
% 0.22/0.53  % (5840)Time elapsed: 0.111 s
% 0.22/0.53  % (5836)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (5840)------------------------------
% 0.22/0.53  % (5840)------------------------------
% 0.22/0.54  % (5830)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (5839)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (5831)Refutation not found, incomplete strategy% (5831)------------------------------
% 0.22/0.54  % (5831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5831)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5831)Memory used [KB]: 1663
% 0.22/0.54  % (5831)Time elapsed: 0.130 s
% 0.22/0.54  % (5831)------------------------------
% 0.22/0.54  % (5831)------------------------------
% 0.22/0.54  % (5844)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5844)Memory used [KB]: 1663
% 0.22/0.54  % (5844)Time elapsed: 0.110 s
% 0.22/0.54  % (5844)------------------------------
% 0.22/0.54  % (5844)------------------------------
% 0.22/0.54  % (5847)Refutation not found, incomplete strategy% (5847)------------------------------
% 0.22/0.54  % (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5847)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5847)Memory used [KB]: 1791
% 0.22/0.54  % (5847)Time elapsed: 0.136 s
% 0.22/0.54  % (5847)------------------------------
% 0.22/0.54  % (5847)------------------------------
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f329,f293])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    sK1 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f290,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f282])).
% 0.22/0.54  fof(f282,plain,(
% 0.22/0.54    sK4 != sK4 | sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(superposition,[],[f34,f267])).
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    sK4 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(resolution,[],[f256,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.54    inference(equality_resolution,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) | sK4 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(resolution,[],[f189,f64])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0))) | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))),
% 0.22/0.54    inference(resolution,[],[f162,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.54    inference(equality_resolution,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.54    inference(equality_resolution,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ( ! [X7] : (~r2_hidden(k2_mcart_1(sK0),X7) | r2_hidden(sK4,X7) | r2_hidden(sK3,X7)) )),
% 0.22/0.54    inference(resolution,[],[f122,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))),
% 0.22/0.54    inference(resolution,[],[f47,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X14,X17,X15,X16] : (~r2_hidden(X17,k2_tarski(X14,X15)) | ~r2_hidden(X17,X16) | r2_hidden(X15,X16) | r2_hidden(X14,X16)) )),
% 0.22/0.54    inference(superposition,[],[f66,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.54    inference(nnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    sK1 = k1_mcart_1(sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f328])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    sK2 != sK2 | sK1 = k1_mcart_1(sK0)),
% 0.22/0.54    inference(superposition,[],[f294,f212])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.22/0.54    inference(resolution,[],[f203,f64])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) | sK2 = k1_mcart_1(sK0)),
% 0.22/0.54    inference(resolution,[],[f176,f64])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0))) | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))),
% 0.22/0.54    inference(resolution,[],[f161,f63])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ( ! [X6] : (~r2_hidden(k1_mcart_1(sK0),X6) | r2_hidden(sK2,X6) | r2_hidden(sK1,X6)) )),
% 0.22/0.54    inference(resolution,[],[f122,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.22/0.54    inference(resolution,[],[f46,f31])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    sK2 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f289,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f283])).
% 0.22/0.54  fof(f283,plain,(
% 0.22/0.54    sK4 != sK4 | sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(superposition,[],[f35,f267])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (5839)------------------------------
% 0.22/0.54  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5839)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (5839)Memory used [KB]: 1918
% 0.22/0.54  % (5839)Time elapsed: 0.125 s
% 0.22/0.54  % (5839)------------------------------
% 0.22/0.54  % (5839)------------------------------
% 0.22/0.54  % (5852)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (5829)Success in time 0.176 s
%------------------------------------------------------------------------------
