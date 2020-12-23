%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   15
%              Number of atoms          :  203 ( 352 expanded)
%              Number of equality atoms :  124 ( 217 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f159,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f71,f132])).

fof(f132,plain,(
    k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f87,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f87,plain,(
    ! [X4] :
      ( r1_tarski(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X4)),X4)
      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X4)
      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

% (25511)Termination reason: Refutation not found, incomplete strategy

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (25511)Memory used [KB]: 10618
% (25511)Time elapsed: 0.127 s
fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),X0)
      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | k1_zfmisc_1(k1_xboole_0) != X0 ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_zfmisc_1(k1_xboole_0) != X0
      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)
      | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),X0) ) ),
    inference(superposition,[],[f40,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) = X2
      | sK1(X0,X1,X2,X3) = X1
      | sK1(X0,X1,X2,X3) = X0
      | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f21])).

% (25511)------------------------------
% (25511)------------------------------
fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f40,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f71,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X1)),X1)
      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1)
      | k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1),X1)
      | k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)
      | k1_zfmisc_1(k1_xboole_0) != X1 ) ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK1(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (25510)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (25511)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25530)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (25523)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (25522)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (25530)Refutation not found, incomplete strategy% (25530)------------------------------
% 0.21/0.52  % (25530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25530)Memory used [KB]: 1663
% 0.21/0.52  % (25530)Time elapsed: 0.062 s
% 0.21/0.52  % (25530)------------------------------
% 0.21/0.52  % (25530)------------------------------
% 0.21/0.53  % (25515)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (25518)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (25534)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (25537)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (25532)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (25534)Refutation not found, incomplete strategy% (25534)------------------------------
% 0.21/0.53  % (25534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25534)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25534)Memory used [KB]: 6268
% 0.21/0.53  % (25534)Time elapsed: 0.128 s
% 0.21/0.53  % (25534)------------------------------
% 0.21/0.53  % (25534)------------------------------
% 0.21/0.53  % (25525)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (25529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (25511)Refutation not found, incomplete strategy% (25511)------------------------------
% 0.21/0.54  % (25511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25509)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (25526)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (25509)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f159,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 != k1_xboole_0),
% 0.21/0.54    inference(superposition,[],[f71,f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    inference(resolution,[],[f87,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X4] : (r1_tarski(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X4)),X4) | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X4) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X4))) )),
% 0.21/0.54    inference(resolution,[],[f55,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  % (25511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (25511)Memory used [KB]: 10618
% 0.21/0.54  % (25511)Time elapsed: 0.127 s
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),X0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | k1_zfmisc_1(k1_xboole_0) != X0) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (k1_zfmisc_1(k1_xboole_0) != X0 | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) | r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),X0)) )),
% 0.21/0.54    inference(superposition,[],[f40,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  % (25511)------------------------------
% 0.21/0.54  % (25511)------------------------------
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(rectify,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) != k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tarski(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1) | k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(resolution,[],[f52,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1),X1) | k1_xboole_0 != sK1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1) | k1_zfmisc_1(k1_xboole_0) != X1) )),
% 0.21/0.54    inference(superposition,[],[f40,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK1(X0,X1,X2,X3) != X0 | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (25509)------------------------------
% 0.21/0.54  % (25509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25509)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (25509)Memory used [KB]: 1791
% 0.21/0.54  % (25509)Time elapsed: 0.126 s
% 0.21/0.54  % (25509)------------------------------
% 0.21/0.54  % (25509)------------------------------
% 0.21/0.54  % (25508)Success in time 0.179 s
%------------------------------------------------------------------------------
