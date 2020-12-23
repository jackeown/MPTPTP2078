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
% DateTime   : Thu Dec  3 12:43:22 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 245 expanded)
%              Number of leaves         :    6 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  174 (1480 expanded)
%              Number of equality atoms :   38 ( 343 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f590,plain,(
    $false ),
    inference(subsumption_resolution,[],[f589,f588])).

fof(f588,plain,(
    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(subsumption_resolution,[],[f581,f25])).

fof(f25,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f581,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(resolution,[],[f577,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f577,plain,(
    ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f576,f65])).

fof(f65,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,k1_tarski(sK3)) ) ),
    inference(superposition,[],[f37,f23])).

fof(f23,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f576,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f571,f25])).

fof(f571,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(resolution,[],[f570,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f570,plain,(
    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) ),
    inference(subsumption_resolution,[],[f569,f97])).

fof(f97,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK0)
      | ~ r2_hidden(X5,k1_tarski(sK3)) ) ),
    inference(superposition,[],[f37,f44])).

fof(f44,plain,(
    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f24,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f569,plain,
    ( r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_tarski(sK3) != X0
      | r2_hidden(sK4(sK0,sK2,X0),sK0)
      | r2_hidden(sK4(sK0,sK2,X0),X0) ) ),
    inference(superposition,[],[f25,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f589,plain,(
    ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(subsumption_resolution,[],[f582,f570])).

fof(f582,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)
    | ~ r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) ),
    inference(resolution,[],[f577,f398])).

fof(f398,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(sK3))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f75,f23])).

fof(f75,plain,(
    ! [X8,X7] :
      ( r2_hidden(X7,k3_xboole_0(sK1,X8))
      | ~ r2_hidden(X7,sK0)
      | ~ r2_hidden(X7,X8) ) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f37,f39])).

fof(f39,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f22,f35])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:10:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.49  % (3622)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.49  % (3639)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.49  % (3613)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (3637)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (3616)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.53  % (3623)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (3630)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (3610)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.56  % (3641)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.57  % (3633)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.57  % (3625)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.57  % (3618)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.60  % (3612)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.96/0.61  % (3635)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.96/0.61  % (3614)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.96/0.61  % (3627)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.96/0.61  % (3621)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.96/0.61  % (3627)Refutation not found, incomplete strategy% (3627)------------------------------
% 1.96/0.61  % (3627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.61  % (3627)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.61  
% 1.96/0.61  % (3627)Memory used [KB]: 6140
% 1.96/0.61  % (3627)Time elapsed: 0.002 s
% 1.96/0.61  % (3627)------------------------------
% 1.96/0.61  % (3627)------------------------------
% 2.09/0.62  % (3636)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.12/0.63  % (3620)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.12/0.63  % (3610)Refutation found. Thanks to Tanya!
% 2.12/0.63  % SZS status Theorem for theBenchmark
% 2.12/0.63  % SZS output start Proof for theBenchmark
% 2.12/0.63  fof(f590,plain,(
% 2.12/0.63    $false),
% 2.12/0.63    inference(subsumption_resolution,[],[f589,f588])).
% 2.12/0.63  fof(f588,plain,(
% 2.12/0.63    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)),
% 2.12/0.63    inference(subsumption_resolution,[],[f581,f25])).
% 2.12/0.63  fof(f25,plain,(
% 2.12/0.63    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.12/0.63    inference(cnf_transformation,[],[f15])).
% 2.12/0.63  fof(f15,plain,(
% 2.12/0.63    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).
% 2.12/0.63  fof(f14,plain,(
% 2.12/0.63    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f12,plain,(
% 2.12/0.63    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.12/0.63    inference(flattening,[],[f11])).
% 2.12/0.63  fof(f11,plain,(
% 2.12/0.63    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.12/0.63    inference(ennf_transformation,[],[f10])).
% 2.12/0.63  fof(f10,negated_conjecture,(
% 2.12/0.63    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.12/0.63    inference(negated_conjecture,[],[f9])).
% 2.12/0.63  fof(f9,conjecture,(
% 2.12/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.12/0.63  fof(f581,plain,(
% 2.12/0.63    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)),
% 2.12/0.63    inference(resolution,[],[f577,f30])).
% 2.12/0.63  fof(f30,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f20,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 2.12/0.63  fof(f19,plain,(
% 2.12/0.63    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f18,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.12/0.63    inference(rectify,[],[f17])).
% 2.12/0.63  fof(f17,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.12/0.63    inference(flattening,[],[f16])).
% 2.12/0.63  fof(f16,plain,(
% 2.12/0.63    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.12/0.63    inference(nnf_transformation,[],[f1])).
% 2.12/0.63  fof(f1,axiom,(
% 2.12/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.12/0.63  fof(f577,plain,(
% 2.12/0.63    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 2.12/0.63    inference(subsumption_resolution,[],[f576,f65])).
% 2.12/0.63  fof(f65,plain,(
% 2.12/0.63    ( ! [X5] : (r2_hidden(X5,sK2) | ~r2_hidden(X5,k1_tarski(sK3))) )),
% 2.12/0.63    inference(superposition,[],[f37,f23])).
% 2.12/0.63  fof(f23,plain,(
% 2.12/0.63    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 2.12/0.63    inference(cnf_transformation,[],[f15])).
% 2.12/0.63  fof(f37,plain,(
% 2.12/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.12/0.63    inference(equality_resolution,[],[f27])).
% 2.12/0.63  fof(f27,plain,(
% 2.12/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f576,plain,(
% 2.12/0.63    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 2.12/0.63    inference(subsumption_resolution,[],[f571,f25])).
% 2.12/0.63  fof(f571,plain,(
% 2.12/0.63    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 2.12/0.63    inference(resolution,[],[f570,f31])).
% 2.12/0.63  fof(f31,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f570,plain,(
% 2.12/0.63    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0)),
% 2.12/0.63    inference(subsumption_resolution,[],[f569,f97])).
% 2.12/0.63  fof(f97,plain,(
% 2.12/0.63    ( ! [X5] : (r2_hidden(X5,sK0) | ~r2_hidden(X5,k1_tarski(sK3))) )),
% 2.12/0.63    inference(superposition,[],[f37,f44])).
% 2.12/0.63  fof(f44,plain,(
% 2.12/0.63    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 2.12/0.63    inference(resolution,[],[f40,f35])).
% 2.12/0.63  fof(f35,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f13])).
% 2.12/0.63  fof(f13,plain,(
% 2.12/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.12/0.63    inference(ennf_transformation,[],[f3])).
% 2.12/0.63  fof(f3,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.12/0.63  fof(f40,plain,(
% 2.12/0.63    r1_tarski(k1_tarski(sK3),sK0)),
% 2.12/0.63    inference(resolution,[],[f24,f33])).
% 2.12/0.63  fof(f33,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f21])).
% 2.12/0.63  fof(f21,plain,(
% 2.12/0.63    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.12/0.63    inference(nnf_transformation,[],[f8])).
% 2.12/0.63  fof(f8,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.12/0.63  fof(f24,plain,(
% 2.12/0.63    r2_hidden(sK3,sK0)),
% 2.12/0.63    inference(cnf_transformation,[],[f15])).
% 2.12/0.63  fof(f569,plain,(
% 2.12/0.63    r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),k1_tarski(sK3))),
% 2.12/0.63    inference(equality_resolution,[],[f68])).
% 2.12/0.63  fof(f68,plain,(
% 2.12/0.63    ( ! [X0] : (k1_tarski(sK3) != X0 | r2_hidden(sK4(sK0,sK2,X0),sK0) | r2_hidden(sK4(sK0,sK2,X0),X0)) )),
% 2.12/0.63    inference(superposition,[],[f25,f29])).
% 2.12/0.63  fof(f29,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f589,plain,(
% 2.12/0.63    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)),
% 2.12/0.63    inference(subsumption_resolution,[],[f582,f570])).
% 2.12/0.63  fof(f582,plain,(
% 2.12/0.63    ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK0) | ~r2_hidden(sK4(sK0,sK2,k1_tarski(sK3)),sK2)),
% 2.12/0.63    inference(resolution,[],[f577,f398])).
% 2.12/0.63  fof(f398,plain,(
% 2.12/0.63    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK3)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) )),
% 2.12/0.63    inference(superposition,[],[f75,f23])).
% 2.12/0.63  fof(f75,plain,(
% 2.12/0.63    ( ! [X8,X7] : (r2_hidden(X7,k3_xboole_0(sK1,X8)) | ~r2_hidden(X7,sK0) | ~r2_hidden(X7,X8)) )),
% 2.12/0.63    inference(resolution,[],[f53,f36])).
% 2.12/0.63  fof(f36,plain,(
% 2.12/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.12/0.63    inference(equality_resolution,[],[f28])).
% 2.12/0.63  fof(f28,plain,(
% 2.12/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f53,plain,(
% 2.12/0.63    ( ! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,sK0)) )),
% 2.12/0.63    inference(superposition,[],[f37,f39])).
% 2.12/0.63  fof(f39,plain,(
% 2.12/0.63    sK0 = k3_xboole_0(sK0,sK1)),
% 2.12/0.63    inference(resolution,[],[f22,f35])).
% 2.12/0.63  fof(f22,plain,(
% 2.12/0.63    r1_tarski(sK0,sK1)),
% 2.12/0.63    inference(cnf_transformation,[],[f15])).
% 2.12/0.63  % SZS output end Proof for theBenchmark
% 2.12/0.63  % (3610)------------------------------
% 2.12/0.63  % (3610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.63  % (3610)Termination reason: Refutation
% 2.12/0.63  
% 2.12/0.63  % (3610)Memory used [KB]: 2174
% 2.12/0.63  % (3610)Time elapsed: 0.226 s
% 2.12/0.63  % (3610)------------------------------
% 2.12/0.63  % (3610)------------------------------
% 2.12/0.63  % (3607)Success in time 0.282 s
%------------------------------------------------------------------------------
