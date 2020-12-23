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
% DateTime   : Thu Dec  3 12:38:55 EST 2020

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 206 expanded)
%              Number of leaves         :    7 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  102 ( 583 expanded)
%              Number of equality atoms :   20 ( 123 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(resolution,[],[f434,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f434,plain,(
    r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f271,f340])).

fof(f340,plain,(
    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) ),
    inference(resolution,[],[f269,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1)
      | k3_tarski(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f269,plain,(
    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2) ),
    inference(superposition,[],[f58,f210])).

fof(f210,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(resolution,[],[f205,f73])).

fof(f73,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f205,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X2,X1))
      | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ) ),
    inference(resolution,[],[f202,f75])).

fof(f75,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f61,f67])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X1,X1,X0))
      | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
      | ~ r2_hidden(X0,k1_enumset1(X1,X1,X0)) ) ),
    inference(resolution,[],[f161,f73])).

fof(f161,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_enumset1(X3,X3,X4))
      | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3)
      | ~ r2_hidden(X4,k1_enumset1(X5,X5,X3))
      | ~ r2_hidden(X3,k1_enumset1(X5,X5,X3)) ) ),
    inference(resolution,[],[f104,f75])).

fof(f104,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(X10,k1_enumset1(X8,X8,X9))
      | k1_enumset1(X8,X8,X9) = k1_enumset1(X7,X7,X10)
      | ~ r2_hidden(X7,k1_enumset1(X8,X8,X9))
      | ~ r2_hidden(X9,k1_enumset1(X7,X7,X10))
      | ~ r2_hidden(X8,k1_enumset1(X7,X7,X10)) ) ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X7,k1_enumset1(X8,X8,X6))
      | ~ r2_hidden(X8,X7)
      | k1_enumset1(X8,X8,X6) = X7
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f59,f41])).

fof(f58,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f34,f53,f50])).

fof(f34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f271,plain,(
    ! [X405,X407,X406] : r2_hidden(X405,k3_tarski(k1_enumset1(X407,X407,k1_enumset1(X405,X405,X406)))) ),
    inference(superposition,[],[f76,f210])).

fof(f76,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4))) ),
    inference(resolution,[],[f61,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:14:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.23/0.53  % (28794)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.53  % (28810)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.53  % (28792)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (28802)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.53  % (28802)Refutation not found, incomplete strategy% (28802)------------------------------
% 1.23/0.53  % (28802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (28802)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (28802)Memory used [KB]: 10618
% 1.23/0.53  % (28802)Time elapsed: 0.099 s
% 1.23/0.53  % (28802)------------------------------
% 1.23/0.53  % (28802)------------------------------
% 1.23/0.54  % (28810)Refutation not found, incomplete strategy% (28810)------------------------------
% 1.23/0.54  % (28810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (28810)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (28810)Memory used [KB]: 10746
% 1.23/0.54  % (28810)Time elapsed: 0.103 s
% 1.23/0.54  % (28810)------------------------------
% 1.23/0.54  % (28810)------------------------------
% 1.38/0.55  % (28793)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (28800)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.55  % (28800)Refutation not found, incomplete strategy% (28800)------------------------------
% 1.38/0.55  % (28800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (28800)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (28800)Memory used [KB]: 1663
% 1.38/0.55  % (28800)Time elapsed: 0.126 s
% 1.38/0.55  % (28800)------------------------------
% 1.38/0.55  % (28800)------------------------------
% 1.38/0.55  % (28808)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (28811)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (28801)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (28788)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.55  % (28799)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.55  % (28814)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.56  % (28786)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.56  % (28791)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.56  % (28789)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.56  % (28812)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (28798)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.56  % (28812)Refutation not found, incomplete strategy% (28812)------------------------------
% 1.38/0.56  % (28812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28812)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (28812)Memory used [KB]: 6268
% 1.38/0.56  % (28812)Time elapsed: 0.143 s
% 1.38/0.56  % (28812)------------------------------
% 1.38/0.56  % (28812)------------------------------
% 1.38/0.56  % (28798)Refutation not found, incomplete strategy% (28798)------------------------------
% 1.38/0.56  % (28798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28798)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (28798)Memory used [KB]: 10618
% 1.38/0.56  % (28798)Time elapsed: 0.143 s
% 1.38/0.56  % (28798)------------------------------
% 1.38/0.56  % (28798)------------------------------
% 1.38/0.56  % (28815)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (28790)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.56  % (28809)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.56  % (28813)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.56  % (28815)Refutation not found, incomplete strategy% (28815)------------------------------
% 1.38/0.56  % (28815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (28815)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (28815)Memory used [KB]: 1663
% 1.38/0.56  % (28815)Time elapsed: 0.146 s
% 1.38/0.56  % (28815)------------------------------
% 1.38/0.56  % (28815)------------------------------
% 1.38/0.56  % (28811)Refutation not found, incomplete strategy% (28811)------------------------------
% 1.38/0.56  % (28811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28813)Refutation not found, incomplete strategy% (28813)------------------------------
% 1.38/0.57  % (28813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28813)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (28813)Memory used [KB]: 6268
% 1.38/0.57  % (28813)Time elapsed: 0.146 s
% 1.38/0.57  % (28813)------------------------------
% 1.38/0.57  % (28813)------------------------------
% 1.38/0.57  % (28807)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.57  % (28796)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.57  % (28805)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.57  % (28811)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (28811)Memory used [KB]: 6268
% 1.38/0.57  % (28811)Time elapsed: 0.111 s
% 1.38/0.57  % (28811)------------------------------
% 1.38/0.57  % (28811)------------------------------
% 1.38/0.57  % (28796)Refutation not found, incomplete strategy% (28796)------------------------------
% 1.38/0.57  % (28796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28796)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (28796)Memory used [KB]: 10874
% 1.38/0.57  % (28796)Time elapsed: 0.146 s
% 1.38/0.57  % (28796)------------------------------
% 1.38/0.57  % (28796)------------------------------
% 1.38/0.57  % (28797)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.57  % (28806)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.57  % (28804)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.57  % (28814)Refutation not found, incomplete strategy% (28814)------------------------------
% 1.38/0.57  % (28814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28803)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.57  % (28795)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.57  % (28787)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.58  % (28797)Refutation not found, incomplete strategy% (28797)------------------------------
% 1.38/0.58  % (28797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (28797)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (28797)Memory used [KB]: 6396
% 1.38/0.58  % (28797)Time elapsed: 0.151 s
% 1.38/0.58  % (28797)------------------------------
% 1.38/0.58  % (28797)------------------------------
% 1.38/0.58  % (28787)Refutation not found, incomplete strategy% (28787)------------------------------
% 1.38/0.58  % (28787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (28787)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (28787)Memory used [KB]: 1663
% 1.38/0.58  % (28787)Time elapsed: 0.123 s
% 1.38/0.58  % (28787)------------------------------
% 1.38/0.58  % (28787)------------------------------
% 1.38/0.58  % (28804)Refutation not found, incomplete strategy% (28804)------------------------------
% 1.38/0.58  % (28804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (28804)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (28804)Memory used [KB]: 1663
% 1.38/0.58  % (28804)Time elapsed: 0.150 s
% 1.38/0.58  % (28804)------------------------------
% 1.38/0.58  % (28804)------------------------------
% 1.38/0.59  % (28814)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.59  
% 1.38/0.59  % (28814)Memory used [KB]: 10874
% 1.38/0.59  % (28814)Time elapsed: 0.153 s
% 1.38/0.59  % (28814)------------------------------
% 1.38/0.59  % (28814)------------------------------
% 1.38/0.59  % (28803)Refutation not found, incomplete strategy% (28803)------------------------------
% 1.38/0.59  % (28803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.59  % (28803)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.59  
% 1.38/0.59  % (28803)Memory used [KB]: 1918
% 1.38/0.59  % (28803)Time elapsed: 0.136 s
% 1.38/0.59  % (28803)------------------------------
% 1.38/0.59  % (28803)------------------------------
% 1.90/0.65  % (28801)Refutation not found, incomplete strategy% (28801)------------------------------
% 1.90/0.65  % (28801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.65  % (28816)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.90/0.66  % (28817)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.90/0.66  % (28794)Refutation not found, incomplete strategy% (28794)------------------------------
% 1.90/0.66  % (28794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.66  % (28794)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.66  
% 1.90/0.66  % (28794)Memory used [KB]: 6268
% 1.90/0.66  % (28794)Time elapsed: 0.214 s
% 1.90/0.66  % (28794)------------------------------
% 1.90/0.66  % (28794)------------------------------
% 1.90/0.66  % (28801)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.66  
% 1.90/0.66  % (28801)Memory used [KB]: 6140
% 1.90/0.66  % (28801)Time elapsed: 0.220 s
% 1.90/0.67  % (28801)------------------------------
% 1.90/0.67  % (28801)------------------------------
% 1.90/0.67  % (28786)Refutation not found, incomplete strategy% (28786)------------------------------
% 1.90/0.67  % (28786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.67  % (28819)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.90/0.67  % (28819)Refutation not found, incomplete strategy% (28819)------------------------------
% 1.90/0.67  % (28819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.67  % (28819)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.67  
% 1.90/0.68  % (28819)Memory used [KB]: 10618
% 1.90/0.68  % (28819)Time elapsed: 0.082 s
% 1.90/0.68  % (28819)------------------------------
% 1.90/0.68  % (28819)------------------------------
% 2.17/0.68  % (28786)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (28786)Memory used [KB]: 1791
% 2.17/0.68  % (28786)Time elapsed: 0.243 s
% 2.17/0.68  % (28786)------------------------------
% 2.17/0.68  % (28786)------------------------------
% 2.17/0.68  % (28828)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.17/0.68  % (28818)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.69  % (28821)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.17/0.69  % (28818)Refutation not found, incomplete strategy% (28818)------------------------------
% 2.17/0.69  % (28818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (28818)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (28818)Memory used [KB]: 6268
% 2.17/0.69  % (28818)Time elapsed: 0.108 s
% 2.17/0.69  % (28818)------------------------------
% 2.17/0.69  % (28818)------------------------------
% 2.17/0.69  % (28828)Refutation not found, incomplete strategy% (28828)------------------------------
% 2.17/0.69  % (28828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (28789)Refutation not found, incomplete strategy% (28789)------------------------------
% 2.17/0.69  % (28789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (28789)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (28789)Memory used [KB]: 6140
% 2.17/0.69  % (28789)Time elapsed: 0.259 s
% 2.17/0.69  % (28789)------------------------------
% 2.17/0.69  % (28789)------------------------------
% 2.17/0.69  % (28828)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (28828)Memory used [KB]: 10746
% 2.17/0.69  % (28828)Time elapsed: 0.058 s
% 2.17/0.69  % (28828)------------------------------
% 2.17/0.69  % (28828)------------------------------
% 2.17/0.70  % (28824)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.17/0.70  % (28820)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.17/0.70  % (28822)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.17/0.70  % (28820)Refutation not found, incomplete strategy% (28820)------------------------------
% 2.17/0.70  % (28820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.70  % (28823)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.17/0.70  % (28822)Refutation not found, incomplete strategy% (28822)------------------------------
% 2.17/0.70  % (28822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (28788)Refutation not found, incomplete strategy% (28788)------------------------------
% 2.17/0.71  % (28788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (28788)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (28788)Memory used [KB]: 6396
% 2.17/0.71  % (28788)Time elapsed: 0.259 s
% 2.17/0.71  % (28788)------------------------------
% 2.17/0.71  % (28788)------------------------------
% 2.17/0.71  % (28825)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.17/0.71  % (28831)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.17/0.71  % (28822)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (28822)Memory used [KB]: 10746
% 2.17/0.71  % (28822)Time elapsed: 0.110 s
% 2.17/0.71  % (28822)------------------------------
% 2.17/0.71  % (28822)------------------------------
% 2.17/0.71  % (28821)Refutation not found, incomplete strategy% (28821)------------------------------
% 2.17/0.71  % (28821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (28821)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (28821)Memory used [KB]: 1791
% 2.17/0.71  % (28821)Time elapsed: 0.120 s
% 2.17/0.71  % (28821)------------------------------
% 2.17/0.71  % (28821)------------------------------
% 2.17/0.71  % (28825)Refutation not found, incomplete strategy% (28825)------------------------------
% 2.17/0.71  % (28825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (28825)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (28825)Memory used [KB]: 10746
% 2.17/0.71  % (28825)Time elapsed: 0.112 s
% 2.17/0.71  % (28825)------------------------------
% 2.17/0.71  % (28825)------------------------------
% 2.17/0.72  % (28820)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.72  
% 2.17/0.72  % (28820)Memory used [KB]: 10746
% 2.17/0.72  % (28820)Time elapsed: 0.112 s
% 2.17/0.72  % (28820)------------------------------
% 2.17/0.72  % (28820)------------------------------
% 2.17/0.72  % (28826)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.17/0.73  % (28836)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.73  % (28836)Refutation not found, incomplete strategy% (28836)------------------------------
% 2.17/0.73  % (28836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.75  % (28836)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.75  
% 2.17/0.75  % (28836)Memory used [KB]: 10746
% 2.17/0.75  % (28836)Time elapsed: 0.118 s
% 2.17/0.75  % (28836)------------------------------
% 2.17/0.75  % (28836)------------------------------
% 2.79/0.77  % (28871)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.79/0.78  % (28867)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.79/0.78  % (28875)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.79/0.78  % (28889)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.79/0.78  % (28872)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.79/0.80  % (28831)Refutation found. Thanks to Tanya!
% 2.79/0.80  % SZS status Theorem for theBenchmark
% 2.79/0.80  % SZS output start Proof for theBenchmark
% 2.79/0.80  fof(f797,plain,(
% 2.79/0.80    $false),
% 2.79/0.80    inference(resolution,[],[f434,f35])).
% 2.79/0.80  fof(f35,plain,(
% 2.79/0.80    ~r2_hidden(sK0,sK2)),
% 2.79/0.80    inference(cnf_transformation,[],[f29])).
% 2.79/0.80  fof(f29,plain,(
% 2.79/0.80    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.79/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 2.79/0.80  fof(f28,plain,(
% 2.79/0.80    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 2.79/0.80    introduced(choice_axiom,[])).
% 2.79/0.80  fof(f27,plain,(
% 2.79/0.80    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.79/0.80    inference(ennf_transformation,[],[f25])).
% 2.79/0.80  fof(f25,negated_conjecture,(
% 2.79/0.80    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.79/0.80    inference(negated_conjecture,[],[f24])).
% 2.79/0.80  fof(f24,conjecture,(
% 2.79/0.80    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 2.79/0.80  fof(f434,plain,(
% 2.79/0.80    r2_hidden(sK0,sK2)),
% 2.79/0.80    inference(superposition,[],[f271,f340])).
% 2.79/0.80  fof(f340,plain,(
% 2.79/0.80    sK2 = k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1)))),
% 2.79/0.80    inference(resolution,[],[f269,f71])).
% 2.79/0.80  fof(f71,plain,(
% 2.79/0.80    ( ! [X2,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X2)),X1) | k3_tarski(k1_enumset1(X1,X1,X2)) = X1) )),
% 2.79/0.80    inference(resolution,[],[f41,f63])).
% 2.79/0.80  fof(f63,plain,(
% 2.79/0.80    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.79/0.80    inference(definition_unfolding,[],[f43,f53])).
% 2.79/0.80  fof(f53,plain,(
% 2.79/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.79/0.80    inference(definition_unfolding,[],[f51,f50])).
% 2.79/0.80  fof(f50,plain,(
% 2.79/0.80    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.79/0.80    inference(cnf_transformation,[],[f16])).
% 2.79/0.80  fof(f16,axiom,(
% 2.79/0.80    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.79/0.80  fof(f51,plain,(
% 2.79/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.79/0.80    inference(cnf_transformation,[],[f22])).
% 2.79/0.80  fof(f22,axiom,(
% 2.79/0.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.79/0.80  fof(f43,plain,(
% 2.79/0.80    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.79/0.80    inference(cnf_transformation,[],[f6])).
% 2.79/0.80  fof(f6,axiom,(
% 2.79/0.80    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.79/0.80  fof(f41,plain,(
% 2.79/0.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.79/0.80    inference(cnf_transformation,[],[f33])).
% 2.79/0.80  fof(f33,plain,(
% 2.79/0.80    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/0.80    inference(flattening,[],[f32])).
% 2.79/0.80  fof(f32,plain,(
% 2.79/0.80    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.79/0.80    inference(nnf_transformation,[],[f4])).
% 2.79/0.80  fof(f4,axiom,(
% 2.79/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.79/0.80  fof(f269,plain,(
% 2.79/0.80    r1_tarski(k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))),sK2)),
% 2.79/0.80    inference(superposition,[],[f58,f210])).
% 2.79/0.80  fof(f210,plain,(
% 2.79/0.80    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.79/0.80    inference(resolution,[],[f205,f73])).
% 2.79/0.80  fof(f73,plain,(
% 2.79/0.80    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 2.79/0.80    inference(resolution,[],[f60,f67])).
% 2.79/0.80  fof(f67,plain,(
% 2.79/0.80    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.79/0.80    inference(equality_resolution,[],[f40])).
% 2.79/0.80  fof(f40,plain,(
% 2.79/0.80    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.79/0.80    inference(cnf_transformation,[],[f33])).
% 2.79/0.80  fof(f60,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.79/0.80    inference(definition_unfolding,[],[f37,f50])).
% 2.79/0.80  fof(f37,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.79/0.80    inference(cnf_transformation,[],[f31])).
% 2.79/0.80  fof(f31,plain,(
% 2.79/0.80    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.79/0.80    inference(flattening,[],[f30])).
% 2.79/0.80  fof(f30,plain,(
% 2.79/0.80    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.79/0.80    inference(nnf_transformation,[],[f23])).
% 2.79/0.80  fof(f23,axiom,(
% 2.79/0.80    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.79/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.79/0.80  fof(f205,plain,(
% 2.79/0.80    ( ! [X2,X1] : (~r2_hidden(X1,k1_enumset1(X2,X2,X1)) | k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1)) )),
% 2.79/0.80    inference(resolution,[],[f202,f75])).
% 2.79/0.80  fof(f75,plain,(
% 2.79/0.80    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 2.79/0.80    inference(resolution,[],[f61,f67])).
% 2.79/0.80  fof(f61,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.79/0.80    inference(definition_unfolding,[],[f36,f50])).
% 2.79/0.80  fof(f36,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.79/0.80    inference(cnf_transformation,[],[f31])).
% 2.79/0.80  fof(f202,plain,(
% 2.79/0.80    ( ! [X0,X1] : (~r2_hidden(X1,k1_enumset1(X1,X1,X0)) | k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) | ~r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 2.79/0.80    inference(resolution,[],[f161,f73])).
% 2.79/0.80  fof(f161,plain,(
% 2.79/0.80    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_enumset1(X3,X3,X4)) | k1_enumset1(X3,X3,X4) = k1_enumset1(X5,X5,X3) | ~r2_hidden(X4,k1_enumset1(X5,X5,X3)) | ~r2_hidden(X3,k1_enumset1(X5,X5,X3))) )),
% 2.79/0.80    inference(resolution,[],[f104,f75])).
% 2.79/0.80  fof(f104,plain,(
% 2.79/0.80    ( ! [X10,X8,X7,X9] : (~r2_hidden(X10,k1_enumset1(X8,X8,X9)) | k1_enumset1(X8,X8,X9) = k1_enumset1(X7,X7,X10) | ~r2_hidden(X7,k1_enumset1(X8,X8,X9)) | ~r2_hidden(X9,k1_enumset1(X7,X7,X10)) | ~r2_hidden(X8,k1_enumset1(X7,X7,X10))) )),
% 2.79/0.80    inference(resolution,[],[f81,f59])).
% 2.79/0.80  fof(f59,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.79/0.80    inference(definition_unfolding,[],[f38,f50])).
% 2.79/0.80  fof(f38,plain,(
% 2.79/0.80    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.79/0.80    inference(cnf_transformation,[],[f31])).
% 2.79/0.80  fof(f81,plain,(
% 2.79/0.80    ( ! [X6,X8,X7] : (~r1_tarski(X7,k1_enumset1(X8,X8,X6)) | ~r2_hidden(X8,X7) | k1_enumset1(X8,X8,X6) = X7 | ~r2_hidden(X6,X7)) )),
% 2.79/0.80    inference(resolution,[],[f59,f41])).
% 2.79/0.80  fof(f58,plain,(
% 2.79/0.80    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 2.79/0.80    inference(definition_unfolding,[],[f34,f53,f50])).
% 2.79/0.80  fof(f34,plain,(
% 2.79/0.80    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.79/0.80    inference(cnf_transformation,[],[f29])).
% 2.79/0.80  fof(f271,plain,(
% 2.79/0.80    ( ! [X405,X407,X406] : (r2_hidden(X405,k3_tarski(k1_enumset1(X407,X407,k1_enumset1(X405,X405,X406))))) )),
% 2.79/0.80    inference(superposition,[],[f76,f210])).
% 2.79/0.80  fof(f76,plain,(
% 2.79/0.80    ( ! [X4,X2,X3] : (r2_hidden(X2,k3_tarski(k1_enumset1(k1_enumset1(X2,X2,X3),k1_enumset1(X2,X2,X3),X4)))) )),
% 2.79/0.80    inference(resolution,[],[f61,f63])).
% 2.79/0.80  % SZS output end Proof for theBenchmark
% 2.79/0.80  % (28831)------------------------------
% 2.79/0.80  % (28831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.80  % (28831)Termination reason: Refutation
% 2.79/0.80  
% 2.79/0.80  % (28831)Memory used [KB]: 2558
% 2.79/0.80  % (28831)Time elapsed: 0.178 s
% 2.79/0.80  % (28831)------------------------------
% 2.79/0.80  % (28831)------------------------------
% 2.79/0.80  % (28785)Success in time 0.421 s
%------------------------------------------------------------------------------
