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
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 177 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  225 ( 969 expanded)
%              Number of equality atoms :   96 ( 482 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f350])).

fof(f350,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f347,f33])).

fof(f33,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f15])).

fof(f15,plain,
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

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f347,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,
    ( sK4 != sK4
    | sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f35,f322])).

fof(f322,plain,
    ( sK4 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f314,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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

fof(f314,plain,
    ( r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))
    | sK4 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f243,f60])).

fof(f243,plain,
    ( r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0)))
    | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_mcart_1(sK0),X0)
      | r2_hidden(sK4,X0)
      | r2_hidden(sK3,X0) ) ),
    inference(superposition,[],[f78,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f78,plain,(
    ! [X2] : ~ r2_hidden(k2_mcart_1(sK0),k4_xboole_0(X2,k2_tarski(sK3,sK4))) ),
    inference(resolution,[],[f65,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f65,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4)) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f32,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f354,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f353])).

fof(f353,plain,
    ( sK2 != sK2
    | sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f351,f284])).

fof(f284,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f276,f60])).

fof(f276,plain,
    ( r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))
    | sK2 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f188,f60])).

fof(f188,plain,
    ( r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0)))
    | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) ),
    inference(resolution,[],[f90,f59])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_mcart_1(sK0),X0)
      | r2_hidden(sK2,X0)
      | r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f73,f57])).

fof(f73,plain,(
    ! [X2] : ~ r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X2,k2_tarski(sK1,sK2))) ),
    inference(resolution,[],[f64,f62])).

fof(f64,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f351,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f346,f34])).

fof(f34,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f346,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f333])).

fof(f333,plain,
    ( sK4 != sK4
    | sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f36,f322])).

fof(f36,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (20578)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (20599)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (20590)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (20579)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (20581)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (20603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (20577)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (20574)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (20574)Refutation not found, incomplete strategy% (20574)------------------------------
% 0.21/0.51  % (20574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20574)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20574)Memory used [KB]: 1663
% 0.21/0.51  % (20574)Time elapsed: 0.098 s
% 0.21/0.51  % (20574)------------------------------
% 0.21/0.51  % (20574)------------------------------
% 0.21/0.51  % (20589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (20587)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (20576)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (20578)Refutation not found, incomplete strategy% (20578)------------------------------
% 0.21/0.52  % (20578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20578)Memory used [KB]: 6140
% 0.21/0.52  % (20578)Time elapsed: 0.111 s
% 0.21/0.52  % (20578)------------------------------
% 0.21/0.52  % (20578)------------------------------
% 0.21/0.52  % (20586)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (20586)Refutation not found, incomplete strategy% (20586)------------------------------
% 0.21/0.52  % (20586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (20586)Memory used [KB]: 10618
% 0.21/0.52  % (20586)Time elapsed: 0.114 s
% 0.21/0.52  % (20586)------------------------------
% 0.21/0.52  % (20586)------------------------------
% 0.21/0.52  % (20604)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (20599)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f354,f350])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    sK1 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f347,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f332])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    sK4 != sK4 | sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(superposition,[],[f35,f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    sK4 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f314,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0))) | sK4 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f243,f60])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    r2_hidden(sK4,k1_tarski(k2_mcart_1(sK0))) | r2_hidden(sK3,k1_tarski(k2_mcart_1(sK0)))),
% 0.21/0.52    inference(resolution,[],[f103,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(k2_mcart_1(sK0),X0) | r2_hidden(sK4,X0) | r2_hidden(sK3,X0)) )),
% 0.21/0.52    inference(superposition,[],[f78,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(k2_mcart_1(sK0),k4_xboole_0(X2,k2_tarski(sK3,sK4)))) )),
% 0.21/0.52    inference(resolution,[],[f65,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK3,sK4))),
% 0.21/0.52    inference(resolution,[],[f32,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    sK1 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f353])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    sK2 != sK2 | sK1 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(superposition,[],[f351,f284])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f276,f60])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0))) | sK2 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f188,f60])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    r2_hidden(sK2,k1_tarski(k1_mcart_1(sK0))) | r2_hidden(sK1,k1_tarski(k1_mcart_1(sK0)))),
% 0.21/0.52    inference(resolution,[],[f90,f59])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK0),X0) | r2_hidden(sK2,X0) | r2_hidden(sK1,X0)) )),
% 0.21/0.52    inference(superposition,[],[f73,f57])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(k1_mcart_1(sK0),k4_xboole_0(X2,k2_tarski(sK1,sK2)))) )),
% 0.21/0.52    inference(resolution,[],[f64,f62])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.52    inference(resolution,[],[f32,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    sK2 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f346,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f333])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    sK4 != sK4 | sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.52    inference(superposition,[],[f36,f322])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20599)------------------------------
% 0.21/0.52  % (20599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20599)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20599)Memory used [KB]: 2046
% 0.21/0.52  % (20599)Time elapsed: 0.063 s
% 0.21/0.52  % (20599)------------------------------
% 0.21/0.52  % (20599)------------------------------
% 1.28/0.52  % (20571)Success in time 0.161 s
%------------------------------------------------------------------------------
