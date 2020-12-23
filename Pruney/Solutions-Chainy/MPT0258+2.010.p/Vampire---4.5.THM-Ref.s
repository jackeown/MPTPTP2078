%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:05 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 114 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 ( 655 expanded)
%              Number of equality atoms :   81 ( 169 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f871,plain,(
    $false ),
    inference(subsumption_resolution,[],[f830,f19])).

fof(f19,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f830,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f125,f818])).

fof(f818,plain,(
    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f779,f20])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f779,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)) ),
    inference(superposition,[],[f125,f110])).

fof(f110,plain,
    ( sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2))
    | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)) ),
    inference(resolution,[],[f107,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f107,plain,(
    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))
    | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k2_tarski(sK0,sK2) != X0
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2))
      | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0) ) ),
    inference(superposition,[],[f21,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f21,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f125,plain,(
    ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f124,f107])).

fof(f124,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1)
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))
    | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2] :
      ( k2_tarski(sK0,sK2) != X2
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),sK1)
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),k2_tarski(sK0,sK2))
      | ~ r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),X2) ) ),
    inference(superposition,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.50  % (5466)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.50  % (5469)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.50  % (5461)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (5466)Refutation not found, incomplete strategy% (5466)------------------------------
% 0.23/0.51  % (5466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (5460)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.51  % (5466)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (5466)Memory used [KB]: 10490
% 0.23/0.51  % (5466)Time elapsed: 0.088 s
% 0.23/0.51  % (5466)------------------------------
% 0.23/0.51  % (5466)------------------------------
% 0.23/0.51  % (5459)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.51  % (5460)Refutation not found, incomplete strategy% (5460)------------------------------
% 0.23/0.51  % (5460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (5462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.51  % (5460)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (5460)Memory used [KB]: 10490
% 0.23/0.51  % (5460)Time elapsed: 0.097 s
% 0.23/0.51  % (5460)------------------------------
% 0.23/0.51  % (5460)------------------------------
% 0.23/0.51  % (5483)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (5463)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.51  % (5468)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.51  % (5472)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.52  % (5478)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.52  % (5470)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (5475)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (5467)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (5485)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.52  % (5481)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (5479)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.53  % (5484)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.53  % (5464)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.53  % (5477)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.53  % (5476)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (5471)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.54  % (5482)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.54  % (5480)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.36/0.54  % (5473)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.36/0.55  % (5474)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.58  % (5478)Refutation found. Thanks to Tanya!
% 1.45/0.58  % SZS status Theorem for theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f871,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(subsumption_resolution,[],[f830,f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    r2_hidden(sK0,sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f8])).
% 1.45/0.58  fof(f8,plain,(
% 1.45/0.58    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 1.45/0.58  fof(f7,plain,(
% 1.45/0.58    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f6,plain,(
% 1.45/0.58    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.45/0.58    inference(flattening,[],[f5])).
% 1.45/0.58  fof(f5,plain,(
% 1.45/0.58    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.45/0.58    inference(ennf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.45/0.58    inference(negated_conjecture,[],[f3])).
% 1.45/0.58  fof(f3,conjecture,(
% 1.45/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.45/0.58  fof(f830,plain,(
% 1.45/0.58    ~r2_hidden(sK0,sK1)),
% 1.45/0.58    inference(backward_demodulation,[],[f125,f818])).
% 1.45/0.58  fof(f818,plain,(
% 1.45/0.58    sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(subsumption_resolution,[],[f779,f20])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    r2_hidden(sK2,sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f8])).
% 1.45/0.58  fof(f779,plain,(
% 1.45/0.58    ~r2_hidden(sK2,sK1) | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(superposition,[],[f125,f110])).
% 1.45/0.58  fof(f110,plain,(
% 1.45/0.58    sK2 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)) | sK0 = sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(resolution,[],[f107,f41])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.45/0.58    inference(equality_resolution,[],[f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.45/0.58    inference(cnf_transformation,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 1.45/0.58  fof(f17,plain,(
% 1.45/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f16,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.58    inference(rectify,[],[f15])).
% 1.45/0.58  fof(f15,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.58    inference(flattening,[],[f14])).
% 1.45/0.58  fof(f14,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.58    inference(nnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.45/0.58  fof(f107,plain,(
% 1.45/0.58    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f106])).
% 1.45/0.58  fof(f106,plain,(
% 1.45/0.58    r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(equality_resolution,[],[f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0] : (k2_tarski(sK0,sK2) != X0 | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),k2_tarski(sK0,sK2)) | r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X0),X0)) )),
% 1.45/0.58    inference(superposition,[],[f21,f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).
% 1.45/0.58  fof(f12,plain,(
% 1.45/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f11,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(rectify,[],[f10])).
% 1.45/0.58  fof(f10,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(flattening,[],[f9])).
% 1.45/0.58  fof(f9,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(nnf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f8])).
% 1.45/0.58  fof(f125,plain,(
% 1.45/0.58    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1)),
% 1.45/0.58    inference(subsumption_resolution,[],[f124,f107])).
% 1.45/0.58  fof(f124,plain,(
% 1.45/0.58    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f123])).
% 1.45/0.58  fof(f123,plain,(
% 1.45/0.58    ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,k2_tarski(sK0,sK2)),k2_tarski(sK0,sK2))),
% 1.45/0.58    inference(equality_resolution,[],[f51])).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    ( ! [X2] : (k2_tarski(sK0,sK2) != X2 | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),sK1) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),k2_tarski(sK0,sK2)) | ~r2_hidden(sK3(k2_tarski(sK0,sK2),sK1,X2),X2)) )),
% 1.45/0.58    inference(superposition,[],[f21,f27])).
% 1.45/0.58  fof(f27,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (5478)------------------------------
% 1.45/0.58  % (5478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (5478)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (5478)Memory used [KB]: 2046
% 1.45/0.58  % (5478)Time elapsed: 0.153 s
% 1.45/0.58  % (5478)------------------------------
% 1.45/0.58  % (5478)------------------------------
% 1.45/0.58  % (5458)Success in time 0.21 s
%------------------------------------------------------------------------------
