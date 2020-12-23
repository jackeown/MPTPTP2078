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
% DateTime   : Thu Dec  3 12:32:42 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 115 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 645 expanded)
%              Number of equality atoms :   21 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f932,plain,(
    $false ),
    inference(subsumption_resolution,[],[f919,f127])).

fof(f127,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f28,f126])).

fof(f126,plain,(
    r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f112,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f112,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),sK1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f49,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),k4_xboole_0(sK1,sK2))
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k4_xboole_0(sK1,sK2)) ) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f919,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f29,f887])).

fof(f887,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f886,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f886,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK4(sK0,sK2,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f882])).

fof(f882,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | sK0 = k4_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK4(sK0,sK2,sK0),sK0)
    | ~ r2_hidden(sK4(sK0,sK2,sK0),sK0) ),
    inference(resolution,[],[f844,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f844,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(sK0,X1,sK0),sK2)
      | sK0 = k4_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f284,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f284,plain,(
    ! [X25] :
      ( r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2))
      | sK0 = k4_xboole_0(sK0,X25) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X25] :
      ( r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2))
      | sK0 = k4_xboole_0(sK0,X25)
      | r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2)) ) ),
    inference(resolution,[],[f54,f45])).

fof(f54,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK4(X9,X10,sK0),k4_xboole_0(sK1,sK2))
      | r2_hidden(sK4(X9,X10,sK0),X9)
      | sK0 = k4_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f45,f38])).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (9474)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (9494)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (9475)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9498)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (9473)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (9486)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (9479)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (9478)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (9480)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (9477)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (9471)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (9496)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (9475)Refutation not found, incomplete strategy% (9475)------------------------------
% 0.21/0.52  % (9475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9475)Memory used [KB]: 6140
% 0.21/0.52  % (9475)Time elapsed: 0.118 s
% 0.21/0.52  % (9475)------------------------------
% 0.21/0.52  % (9475)------------------------------
% 0.21/0.52  % (9489)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (9481)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (9495)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (9485)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (9490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (9479)Refutation not found, incomplete strategy% (9479)------------------------------
% 0.21/0.52  % (9479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9479)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9479)Memory used [KB]: 10618
% 0.21/0.52  % (9479)Time elapsed: 0.114 s
% 0.21/0.52  % (9479)------------------------------
% 0.21/0.52  % (9479)------------------------------
% 0.21/0.52  % (9491)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (9473)Refutation not found, incomplete strategy% (9473)------------------------------
% 0.21/0.52  % (9473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9473)Memory used [KB]: 10618
% 0.21/0.52  % (9473)Time elapsed: 0.126 s
% 0.21/0.52  % (9473)------------------------------
% 0.21/0.52  % (9473)------------------------------
% 0.21/0.52  % (9491)Refutation not found, incomplete strategy% (9491)------------------------------
% 0.21/0.52  % (9491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9491)Memory used [KB]: 10618
% 0.21/0.52  % (9491)Time elapsed: 0.131 s
% 0.21/0.52  % (9491)------------------------------
% 0.21/0.52  % (9491)------------------------------
% 0.21/0.53  % (9499)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (9482)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (9497)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (9481)Refutation not found, incomplete strategy% (9481)------------------------------
% 0.21/0.53  % (9481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9481)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9481)Memory used [KB]: 10618
% 0.21/0.53  % (9481)Time elapsed: 0.137 s
% 0.21/0.53  % (9481)------------------------------
% 0.21/0.53  % (9481)------------------------------
% 0.21/0.53  % (9476)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (9496)Refutation not found, incomplete strategy% (9496)------------------------------
% 0.21/0.53  % (9496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9496)Memory used [KB]: 6268
% 0.21/0.53  % (9496)Time elapsed: 0.130 s
% 0.21/0.53  % (9496)------------------------------
% 0.21/0.53  % (9496)------------------------------
% 0.21/0.53  % (9472)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9483)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9493)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (9487)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (9500)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9484)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (9492)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9497)Refutation not found, incomplete strategy% (9497)------------------------------
% 0.21/0.54  % (9497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9497)Memory used [KB]: 10746
% 0.21/0.54  % (9497)Time elapsed: 0.143 s
% 0.21/0.54  % (9497)------------------------------
% 0.21/0.54  % (9497)------------------------------
% 0.21/0.55  % (9492)Refutation not found, incomplete strategy% (9492)------------------------------
% 0.21/0.55  % (9492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9492)Memory used [KB]: 1663
% 0.21/0.55  % (9492)Time elapsed: 0.150 s
% 0.21/0.55  % (9492)------------------------------
% 0.21/0.55  % (9492)------------------------------
% 1.70/0.57  % (9488)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.12/0.63  % (9507)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.12/0.65  % (9505)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.12/0.65  % (9506)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.12/0.65  % (9502)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.34/0.66  % (9508)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.34/0.66  % (9503)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.34/0.67  % (9504)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.34/0.69  % (9509)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.13/0.82  % (9476)Time limit reached!
% 3.13/0.82  % (9476)------------------------------
% 3.13/0.82  % (9476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (9502)Refutation found. Thanks to Tanya!
% 3.13/0.82  % SZS status Theorem for theBenchmark
% 3.13/0.82  % SZS output start Proof for theBenchmark
% 3.13/0.82  fof(f932,plain,(
% 3.13/0.82    $false),
% 3.13/0.82    inference(subsumption_resolution,[],[f919,f127])).
% 3.13/0.82  fof(f127,plain,(
% 3.13/0.82    ~r1_xboole_0(sK0,sK2)),
% 3.13/0.82    inference(subsumption_resolution,[],[f28,f126])).
% 3.13/0.82  fof(f126,plain,(
% 3.13/0.82    r1_tarski(sK0,sK1)),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f122])).
% 3.13/0.82  fof(f122,plain,(
% 3.13/0.82    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1)),
% 3.13/0.82    inference(resolution,[],[f112,f32])).
% 3.13/0.82  fof(f32,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f21])).
% 3.13/0.82  fof(f21,plain,(
% 3.13/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 3.13/0.82  fof(f20,plain,(
% 3.13/0.82    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 3.13/0.82    introduced(choice_axiom,[])).
% 3.13/0.82  fof(f19,plain,(
% 3.13/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.82    inference(rectify,[],[f18])).
% 3.13/0.82  fof(f18,plain,(
% 3.13/0.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.13/0.82    inference(nnf_transformation,[],[f15])).
% 3.13/0.82  fof(f15,plain,(
% 3.13/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.13/0.82    inference(ennf_transformation,[],[f1])).
% 3.13/0.82  fof(f1,axiom,(
% 3.13/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.13/0.82  fof(f112,plain,(
% 3.13/0.82    ( ! [X0] : (r2_hidden(sK3(sK0,X0),sK1) | r1_tarski(sK0,X0)) )),
% 3.13/0.82    inference(resolution,[],[f49,f44])).
% 3.13/0.82  fof(f44,plain,(
% 3.13/0.82    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.13/0.82    inference(equality_resolution,[],[f35])).
% 3.13/0.82  fof(f35,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.13/0.82    inference(cnf_transformation,[],[f26])).
% 3.13/0.82  fof(f26,plain,(
% 3.13/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.13/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 3.13/0.82  fof(f25,plain,(
% 3.13/0.82    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 3.13/0.82    introduced(choice_axiom,[])).
% 3.13/0.82  fof(f24,plain,(
% 3.13/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.13/0.82    inference(rectify,[],[f23])).
% 3.13/0.82  fof(f23,plain,(
% 3.13/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.13/0.82    inference(flattening,[],[f22])).
% 3.13/0.82  fof(f22,plain,(
% 3.13/0.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.13/0.82    inference(nnf_transformation,[],[f2])).
% 3.13/0.82  fof(f2,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.13/0.82  fof(f49,plain,(
% 3.13/0.82    ( ! [X0] : (r2_hidden(sK3(sK0,X0),k4_xboole_0(sK1,sK2)) | r1_tarski(sK0,X0)) )),
% 3.13/0.82    inference(resolution,[],[f45,f31])).
% 3.13/0.82  fof(f31,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f21])).
% 3.13/0.82  fof(f45,plain,(
% 3.13/0.82    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k4_xboole_0(sK1,sK2))) )),
% 3.13/0.82    inference(resolution,[],[f27,f30])).
% 3.13/0.82  fof(f30,plain,(
% 3.13/0.82    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f21])).
% 3.13/0.82  fof(f27,plain,(
% 3.13/0.82    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.13/0.82    inference(cnf_transformation,[],[f17])).
% 3.13/0.82  fof(f17,plain,(
% 3.13/0.82    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.13/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 3.13/0.82  fof(f16,plain,(
% 3.13/0.82    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.13/0.82    introduced(choice_axiom,[])).
% 3.13/0.82  fof(f14,plain,(
% 3.13/0.82    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.13/0.82    inference(ennf_transformation,[],[f13])).
% 3.13/0.82  fof(f13,negated_conjecture,(
% 3.13/0.82    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.13/0.82    inference(negated_conjecture,[],[f12])).
% 3.13/0.82  fof(f12,conjecture,(
% 3.13/0.82    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.13/0.82  fof(f28,plain,(
% 3.13/0.82    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.13/0.82    inference(cnf_transformation,[],[f17])).
% 3.13/0.82  fof(f919,plain,(
% 3.13/0.82    r1_xboole_0(sK0,sK2)),
% 3.13/0.82    inference(superposition,[],[f29,f887])).
% 3.13/0.82  fof(f887,plain,(
% 3.13/0.82    sK0 = k4_xboole_0(sK0,sK2)),
% 3.13/0.82    inference(subsumption_resolution,[],[f886,f38])).
% 3.13/0.82  fof(f38,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f26])).
% 3.13/0.82  fof(f886,plain,(
% 3.13/0.82    sK0 = k4_xboole_0(sK0,sK2) | ~r2_hidden(sK4(sK0,sK2,sK0),sK0)),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f882])).
% 3.13/0.82  fof(f882,plain,(
% 3.13/0.82    sK0 = k4_xboole_0(sK0,sK2) | sK0 = k4_xboole_0(sK0,sK2) | ~r2_hidden(sK4(sK0,sK2,sK0),sK0) | ~r2_hidden(sK4(sK0,sK2,sK0),sK0)),
% 3.13/0.82    inference(resolution,[],[f844,f40])).
% 3.13/0.82  fof(f40,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f26])).
% 3.13/0.82  fof(f844,plain,(
% 3.13/0.82    ( ! [X1] : (~r2_hidden(sK4(sK0,X1,sK0),sK2) | sK0 = k4_xboole_0(sK0,X1)) )),
% 3.13/0.82    inference(resolution,[],[f284,f43])).
% 3.13/0.82  fof(f43,plain,(
% 3.13/0.82    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.13/0.82    inference(equality_resolution,[],[f36])).
% 3.13/0.82  fof(f36,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.13/0.82    inference(cnf_transformation,[],[f26])).
% 3.13/0.82  fof(f284,plain,(
% 3.13/0.82    ( ! [X25] : (r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2)) | sK0 = k4_xboole_0(sK0,X25)) )),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f278])).
% 3.13/0.82  fof(f278,plain,(
% 3.13/0.82    ( ! [X25] : (r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2)) | sK0 = k4_xboole_0(sK0,X25) | r2_hidden(sK4(sK0,X25,sK0),k4_xboole_0(sK1,sK2))) )),
% 3.13/0.82    inference(resolution,[],[f54,f45])).
% 3.13/0.82  fof(f54,plain,(
% 3.13/0.82    ( ! [X10,X9] : (r2_hidden(sK4(X9,X10,sK0),k4_xboole_0(sK1,sK2)) | r2_hidden(sK4(X9,X10,sK0),X9) | sK0 = k4_xboole_0(X9,X10)) )),
% 3.13/0.82    inference(resolution,[],[f45,f38])).
% 3.13/0.82  fof(f29,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f9])).
% 3.13/0.82  fof(f9,axiom,(
% 3.13/0.82    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.13/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.13/0.82  % SZS output end Proof for theBenchmark
% 3.13/0.82  % (9502)------------------------------
% 3.13/0.82  % (9502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (9502)Termination reason: Refutation
% 3.13/0.82  
% 3.13/0.82  % (9502)Memory used [KB]: 7291
% 3.13/0.82  % (9502)Time elapsed: 0.268 s
% 3.13/0.82  % (9502)------------------------------
% 3.13/0.82  % (9502)------------------------------
% 3.13/0.83  % (9470)Success in time 0.469 s
%------------------------------------------------------------------------------
