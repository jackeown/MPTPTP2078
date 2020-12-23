%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:50 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  176 ( 222 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1567,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1544,f117])).

fof(f117,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f104,f49])).

fof(f49,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1))
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1))
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1544,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(superposition,[],[f108,f1522])).

fof(f1522,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f1500,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1500,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f57,f1231])).

fof(f1231,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(resolution,[],[f1228,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f1228,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(duplicate_literal_removal,[],[f1215])).

fof(f1215,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k4_xboole_0(X2,X3),X3)
      | r1_xboole_0(k4_xboole_0(X2,X3),X3) ) ),
    inference(resolution,[],[f133,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f132,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f108,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK2,k1_tarski(sK1))) ),
    inference(superposition,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f50,plain,(
    sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (3749)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (3757)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (3765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (3745)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (3744)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (3766)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (3753)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (3747)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (3760)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (3743)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (3746)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (3758)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (3748)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (3751)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (3771)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (3761)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (3759)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (3763)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (3754)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (3769)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (3772)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (3756)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (3767)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.57  % (3762)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.57  % (3752)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.57  % (3764)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.57  % (3768)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.57/0.58  % (3755)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.58  % (3770)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.58  % (3750)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.76/0.75  % (3750)Refutation found. Thanks to Tanya!
% 2.76/0.75  % SZS status Theorem for theBenchmark
% 2.76/0.75  % SZS output start Proof for theBenchmark
% 2.76/0.75  fof(f1567,plain,(
% 2.76/0.75    $false),
% 2.76/0.75    inference(subsumption_resolution,[],[f1544,f117])).
% 2.76/0.75  fof(f117,plain,(
% 2.76/0.75    sK2 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 2.76/0.75    inference(resolution,[],[f104,f49])).
% 2.76/0.75  fof(f49,plain,(
% 2.76/0.75    r2_hidden(sK1,sK2)),
% 2.76/0.75    inference(cnf_transformation,[],[f31])).
% 2.76/0.75  fof(f31,plain,(
% 2.76/0.75    sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1)) & r2_hidden(sK1,sK2)),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f30])).
% 2.76/0.75  fof(f30,plain,(
% 2.76/0.75    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1)) & r2_hidden(sK1,sK2))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f22,plain,(
% 2.76/0.75    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f20])).
% 2.76/0.75  fof(f20,negated_conjecture,(
% 2.76/0.75    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.76/0.75    inference(negated_conjecture,[],[f19])).
% 2.76/0.75  fof(f19,conjecture,(
% 2.76/0.75    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 2.76/0.75  fof(f104,plain,(
% 2.76/0.75    ( ! [X2,X1] : (~r2_hidden(X1,X2) | k2_xboole_0(k1_tarski(X1),X2) = X2) )),
% 2.76/0.75    inference(resolution,[],[f62,f72])).
% 2.76/0.75  fof(f72,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f41])).
% 2.76/0.75  fof(f41,plain,(
% 2.76/0.75    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.76/0.75    inference(nnf_transformation,[],[f17])).
% 2.76/0.75  fof(f17,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.76/0.75  fof(f62,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.76/0.75    inference(cnf_transformation,[],[f25])).
% 2.76/0.75  fof(f25,plain,(
% 2.76/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f8])).
% 2.76/0.75  fof(f8,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.76/0.75  fof(f1544,plain,(
% 2.76/0.75    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 2.76/0.75    inference(superposition,[],[f108,f1522])).
% 2.76/0.75  fof(f1522,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f1500,f57])).
% 2.76/0.75  fof(f57,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f12])).
% 2.76/0.75  fof(f12,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.76/0.75  fof(f1500,plain,(
% 2.76/0.75    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k5_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 2.76/0.75    inference(superposition,[],[f57,f1231])).
% 2.76/0.75  fof(f1231,plain,(
% 2.76/0.75    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 2.76/0.75    inference(resolution,[],[f1228,f69])).
% 2.76/0.75  fof(f69,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f40])).
% 2.76/0.75  fof(f40,plain,(
% 2.76/0.75    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.76/0.75    inference(nnf_transformation,[],[f11])).
% 2.76/0.75  fof(f11,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.76/0.75  fof(f1228,plain,(
% 2.76/0.75    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 2.76/0.75    inference(duplicate_literal_removal,[],[f1215])).
% 2.76/0.75  fof(f1215,plain,(
% 2.76/0.75    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,X3),X3) | r1_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 2.76/0.75    inference(resolution,[],[f133,f59])).
% 2.76/0.75  fof(f59,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f33,plain,(
% 2.76/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f32])).
% 2.76/0.75  fof(f32,plain,(
% 2.76/0.75    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f23,plain,(
% 2.76/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.76/0.75    inference(ennf_transformation,[],[f21])).
% 2.76/0.75  fof(f21,plain,(
% 2.76/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.76/0.75    inference(rectify,[],[f5])).
% 2.76/0.75  fof(f5,axiom,(
% 2.76/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.76/0.75  fof(f133,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.76/0.75    inference(resolution,[],[f132,f58])).
% 2.76/0.75  fof(f58,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f132,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 2.76/0.75    inference(resolution,[],[f75,f89])).
% 2.76/0.75  fof(f89,plain,(
% 2.76/0.75    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 2.76/0.75    inference(equality_resolution,[],[f80])).
% 2.76/0.75  fof(f80,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.76/0.75    inference(cnf_transformation,[],[f47])).
% 2.76/0.75  fof(f47,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.75    inference(nnf_transformation,[],[f29])).
% 2.76/0.75  fof(f29,plain,(
% 2.76/0.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.76/0.75    inference(definition_folding,[],[f3,f28])).
% 2.76/0.75  fof(f28,plain,(
% 2.76/0.75    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.76/0.75  fof(f3,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.76/0.75  fof(f75,plain,(
% 2.76/0.75    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f46])).
% 2.76/0.75  fof(f46,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 2.76/0.75  fof(f45,plain,(
% 2.76/0.75    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f44,plain,(
% 2.76/0.75    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.76/0.75    inference(rectify,[],[f43])).
% 2.76/0.75  fof(f43,plain,(
% 2.76/0.75    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.76/0.75    inference(flattening,[],[f42])).
% 2.76/0.75  fof(f42,plain,(
% 2.76/0.75    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.76/0.75    inference(nnf_transformation,[],[f28])).
% 2.76/0.75  fof(f108,plain,(
% 2.76/0.75    sK2 != k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK2,k1_tarski(sK1)))),
% 2.76/0.75    inference(superposition,[],[f50,f53])).
% 2.76/0.75  fof(f53,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f1])).
% 2.76/0.75  fof(f1,axiom,(
% 2.76/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.76/0.75  fof(f50,plain,(
% 2.76/0.75    sK2 != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK1))),
% 2.76/0.75    inference(cnf_transformation,[],[f31])).
% 2.76/0.75  % SZS output end Proof for theBenchmark
% 2.76/0.75  % (3750)------------------------------
% 2.76/0.75  % (3750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.75  % (3750)Termination reason: Refutation
% 2.76/0.75  
% 2.76/0.75  % (3750)Memory used [KB]: 7547
% 2.76/0.75  % (3750)Time elapsed: 0.327 s
% 2.76/0.75  % (3750)------------------------------
% 2.76/0.75  % (3750)------------------------------
% 3.20/0.77  % (3742)Success in time 0.414 s
%------------------------------------------------------------------------------
