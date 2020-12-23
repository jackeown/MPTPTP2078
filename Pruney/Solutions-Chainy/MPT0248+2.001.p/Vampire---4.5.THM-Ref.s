%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 726 expanded)
%              Number of leaves         :   14 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  214 (2945 expanded)
%              Number of equality atoms :  120 (1984 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4437,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4436,f4431])).

fof(f4431,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f4325,f4424])).

fof(f4424,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f4316,f4422])).

fof(f4422,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f157,f4325])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f150,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f150,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f67,f93])).

fof(f93,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f57,f47])).

fof(f47,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4316,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f4315])).

fof(f4315,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f54,f4312])).

fof(f4312,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f238,f93])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | sK3(X0) = X1 ) ),
    inference(resolution,[],[f161,f87])).

fof(f87,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f161,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK3(X8),X9)
      | ~ r1_tarski(X8,X9)
      | k1_xboole_0 = X8 ) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f4325,plain,(
    sK1 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f50,f4324])).

fof(f4324,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f49,f48,f163,f4318,f4322])).

fof(f4322,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f4321])).

fof(f4321,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f54,f4313])).

fof(f4313,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f238,f132])).

fof(f132,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f117,f47])).

fof(f117,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f57,f111])).

fof(f111,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f102,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f102,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4318,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f4316,f157])).

fof(f163,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f151,f76])).

fof(f151,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f67,f132])).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f4436,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f4435,f4424])).

fof(f4435,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f4326,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f4326,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f47,f4324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (13906)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (13905)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (13922)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13914)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (13913)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (13921)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (13903)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (13900)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (13927)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (13912)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.53  % (13904)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (13902)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.54  % (13909)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.54  % (13918)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.25/0.54  % (13919)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.54  % (13901)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (13926)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.54  % (13923)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (13917)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (13928)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (13908)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (13915)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (13911)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (13910)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (13920)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (13907)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (13929)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (13924)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (13925)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (13916)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.57  % (13910)Refutation not found, incomplete strategy% (13910)------------------------------
% 1.41/0.57  % (13910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (13910)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (13910)Memory used [KB]: 10618
% 1.41/0.57  % (13910)Time elapsed: 0.169 s
% 1.41/0.57  % (13910)------------------------------
% 1.41/0.57  % (13910)------------------------------
% 2.99/0.75  % (13942)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.12/0.80  % (13907)Refutation found. Thanks to Tanya!
% 3.12/0.80  % SZS status Theorem for theBenchmark
% 3.12/0.80  % SZS output start Proof for theBenchmark
% 3.12/0.80  fof(f4437,plain,(
% 3.12/0.80    $false),
% 3.12/0.80    inference(subsumption_resolution,[],[f4436,f4431])).
% 3.12/0.80  fof(f4431,plain,(
% 3.12/0.80    k1_xboole_0 != k1_tarski(sK0)),
% 3.12/0.80    inference(backward_demodulation,[],[f4325,f4424])).
% 3.12/0.80  fof(f4424,plain,(
% 3.12/0.80    k1_xboole_0 = sK1),
% 3.12/0.80    inference(subsumption_resolution,[],[f4316,f4422])).
% 3.12/0.80  fof(f4422,plain,(
% 3.12/0.80    ~r2_hidden(sK0,sK1)),
% 3.12/0.80    inference(subsumption_resolution,[],[f157,f4325])).
% 3.12/0.80  fof(f157,plain,(
% 3.12/0.80    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 3.12/0.80    inference(resolution,[],[f150,f76])).
% 3.12/0.80  fof(f76,plain,(
% 3.12/0.80    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f46])).
% 3.12/0.80  fof(f46,plain,(
% 3.12/0.80    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.12/0.80    inference(nnf_transformation,[],[f23])).
% 3.12/0.80  fof(f23,axiom,(
% 3.12/0.80    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 3.12/0.80  fof(f150,plain,(
% 3.12/0.80    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 3.12/0.80    inference(resolution,[],[f67,f93])).
% 3.12/0.80  fof(f93,plain,(
% 3.12/0.80    r1_tarski(sK1,k1_tarski(sK0))),
% 3.12/0.80    inference(superposition,[],[f57,f47])).
% 3.12/0.80  fof(f47,plain,(
% 3.12/0.80    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 3.12/0.80    inference(cnf_transformation,[],[f33])).
% 3.12/0.80  fof(f33,plain,(
% 3.12/0.80    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 3.12/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32])).
% 3.12/0.80  fof(f32,plain,(
% 3.12/0.80    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 3.12/0.80    introduced(choice_axiom,[])).
% 3.12/0.80  fof(f29,plain,(
% 3.12/0.80    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.12/0.80    inference(ennf_transformation,[],[f26])).
% 3.12/0.80  fof(f26,negated_conjecture,(
% 3.12/0.80    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.12/0.80    inference(negated_conjecture,[],[f25])).
% 3.12/0.80  fof(f25,conjecture,(
% 3.12/0.80    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 3.12/0.80  fof(f57,plain,(
% 3.12/0.80    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.12/0.80    inference(cnf_transformation,[],[f10])).
% 3.12/0.80  fof(f10,axiom,(
% 3.12/0.80    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.12/0.80  fof(f67,plain,(
% 3.12/0.80    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.12/0.80    inference(cnf_transformation,[],[f37])).
% 3.12/0.80  fof(f37,plain,(
% 3.12/0.80    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.80    inference(flattening,[],[f36])).
% 3.12/0.80  fof(f36,plain,(
% 3.12/0.80    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.12/0.80    inference(nnf_transformation,[],[f6])).
% 3.12/0.80  fof(f6,axiom,(
% 3.12/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.12/0.80  fof(f4316,plain,(
% 3.12/0.80    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 3.12/0.80    inference(duplicate_literal_removal,[],[f4315])).
% 3.12/0.80  fof(f4315,plain,(
% 3.12/0.80    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 3.12/0.80    inference(superposition,[],[f54,f4312])).
% 3.12/0.80  fof(f4312,plain,(
% 3.12/0.80    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 3.12/0.80    inference(resolution,[],[f238,f93])).
% 3.12/0.80  fof(f238,plain,(
% 3.12/0.80    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | sK3(X0) = X1) )),
% 3.12/0.80    inference(resolution,[],[f161,f87])).
% 3.12/0.80  fof(f87,plain,(
% 3.12/0.80    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 3.12/0.80    inference(equality_resolution,[],[f71])).
% 3.12/0.80  fof(f71,plain,(
% 3.12/0.80    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.12/0.80    inference(cnf_transformation,[],[f45])).
% 3.12/0.80  fof(f45,plain,(
% 3.12/0.80    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.12/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 3.12/0.80  fof(f44,plain,(
% 3.12/0.80    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 3.12/0.80    introduced(choice_axiom,[])).
% 3.12/0.80  fof(f43,plain,(
% 3.12/0.80    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.12/0.80    inference(rectify,[],[f42])).
% 3.12/0.80  fof(f42,plain,(
% 3.12/0.80    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.12/0.80    inference(nnf_transformation,[],[f15])).
% 3.12/0.80  fof(f15,axiom,(
% 3.12/0.80    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 3.12/0.80  fof(f161,plain,(
% 3.12/0.80    ( ! [X8,X9] : (r2_hidden(sK3(X8),X9) | ~r1_tarski(X8,X9) | k1_xboole_0 = X8) )),
% 3.12/0.80    inference(resolution,[],[f68,f54])).
% 3.12/0.80  fof(f68,plain,(
% 3.12/0.80    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 3.12/0.80    inference(cnf_transformation,[],[f41])).
% 3.12/0.80  fof(f41,plain,(
% 3.12/0.80    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.12/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 3.12/0.80  fof(f40,plain,(
% 3.12/0.80    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.12/0.80    introduced(choice_axiom,[])).
% 3.12/0.80  fof(f39,plain,(
% 3.12/0.80    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.12/0.80    inference(rectify,[],[f38])).
% 3.12/0.80  fof(f38,plain,(
% 3.12/0.80    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.12/0.80    inference(nnf_transformation,[],[f31])).
% 3.12/0.80  fof(f31,plain,(
% 3.12/0.80    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.12/0.80    inference(ennf_transformation,[],[f2])).
% 3.12/0.80  fof(f2,axiom,(
% 3.12/0.80    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.12/0.80  fof(f54,plain,(
% 3.12/0.80    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 3.12/0.80    inference(cnf_transformation,[],[f35])).
% 3.12/0.80  fof(f35,plain,(
% 3.12/0.80    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 3.12/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f34])).
% 3.12/0.80  fof(f34,plain,(
% 3.12/0.80    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 3.12/0.80    introduced(choice_axiom,[])).
% 3.12/0.80  fof(f30,plain,(
% 3.12/0.80    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.12/0.80    inference(ennf_transformation,[],[f5])).
% 3.12/0.80  fof(f5,axiom,(
% 3.12/0.80    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.12/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 3.12/0.80  fof(f4325,plain,(
% 3.12/0.80    sK1 != k1_tarski(sK0)),
% 3.12/0.80    inference(subsumption_resolution,[],[f50,f4324])).
% 3.12/0.81  fof(f4324,plain,(
% 3.12/0.81    k1_xboole_0 = sK2),
% 3.12/0.81    inference(global_subsumption,[],[f49,f48,f163,f4318,f4322])).
% 3.12/0.81  fof(f4322,plain,(
% 3.12/0.81    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 3.12/0.81    inference(duplicate_literal_removal,[],[f4321])).
% 3.12/0.81  fof(f4321,plain,(
% 3.12/0.81    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 3.12/0.81    inference(superposition,[],[f54,f4313])).
% 3.12/0.81  fof(f4313,plain,(
% 3.12/0.81    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 3.12/0.81    inference(resolution,[],[f238,f132])).
% 3.12/0.81  fof(f132,plain,(
% 3.12/0.81    r1_tarski(sK2,k1_tarski(sK0))),
% 3.12/0.81    inference(superposition,[],[f117,f47])).
% 3.12/0.81  fof(f117,plain,(
% 3.12/0.81    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 3.12/0.81    inference(superposition,[],[f57,f111])).
% 3.12/0.81  fof(f111,plain,(
% 3.12/0.81    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 3.12/0.81    inference(superposition,[],[f102,f61])).
% 3.12/0.81  fof(f61,plain,(
% 3.12/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.12/0.81    inference(cnf_transformation,[],[f24])).
% 3.12/0.81  fof(f24,axiom,(
% 3.12/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.12/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.12/0.81  fof(f102,plain,(
% 3.12/0.81    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 3.12/0.81    inference(superposition,[],[f61,f58])).
% 3.12/0.81  fof(f58,plain,(
% 3.12/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.12/0.81    inference(cnf_transformation,[],[f14])).
% 3.12/0.81  fof(f14,axiom,(
% 3.12/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.12/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.12/0.81  fof(f4318,plain,(
% 3.12/0.81    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 3.12/0.81    inference(resolution,[],[f4316,f157])).
% 3.12/0.81  fof(f163,plain,(
% 3.12/0.81    ~r2_hidden(sK0,sK2) | sK2 = k1_tarski(sK0)),
% 3.12/0.81    inference(resolution,[],[f151,f76])).
% 3.12/0.81  fof(f151,plain,(
% 3.12/0.81    ~r1_tarski(k1_tarski(sK0),sK2) | sK2 = k1_tarski(sK0)),
% 3.12/0.81    inference(resolution,[],[f67,f132])).
% 3.12/0.81  fof(f48,plain,(
% 3.12/0.81    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 3.12/0.81    inference(cnf_transformation,[],[f33])).
% 3.12/0.81  fof(f49,plain,(
% 3.12/0.81    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 3.12/0.81    inference(cnf_transformation,[],[f33])).
% 3.12/0.81  fof(f50,plain,(
% 3.12/0.81    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 3.12/0.81    inference(cnf_transformation,[],[f33])).
% 3.12/0.81  fof(f4436,plain,(
% 3.12/0.81    k1_xboole_0 = k1_tarski(sK0)),
% 3.12/0.81    inference(forward_demodulation,[],[f4435,f4424])).
% 3.12/0.81  fof(f4435,plain,(
% 3.12/0.81    sK1 = k1_tarski(sK0)),
% 3.12/0.81    inference(forward_demodulation,[],[f4326,f52])).
% 3.12/0.81  fof(f52,plain,(
% 3.12/0.81    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.12/0.81    inference(cnf_transformation,[],[f8])).
% 3.12/0.81  fof(f8,axiom,(
% 3.12/0.81    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.12/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.12/0.81  fof(f4326,plain,(
% 3.12/0.81    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 3.12/0.81    inference(backward_demodulation,[],[f47,f4324])).
% 3.12/0.81  % SZS output end Proof for theBenchmark
% 3.12/0.81  % (13907)------------------------------
% 3.12/0.81  % (13907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.81  % (13907)Termination reason: Refutation
% 3.12/0.81  
% 3.12/0.81  % (13907)Memory used [KB]: 9722
% 3.12/0.81  % (13907)Time elapsed: 0.324 s
% 3.12/0.81  % (13907)------------------------------
% 3.12/0.81  % (13907)------------------------------
% 3.12/0.81  % (13899)Success in time 0.45 s
%------------------------------------------------------------------------------
