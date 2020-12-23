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
% DateTime   : Thu Dec  3 12:41:16 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   34 (  98 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 150 expanded)
%              Number of equality atoms :   45 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f112,f90,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f90,plain,(
    r2_hidden(sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f39,plain,(
    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f16,f37,f35,f37])).

fof(f16,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f40,plain,(
    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f15,f35,f37])).

fof(f15,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f112,plain,(
    ! [X0] : ~ sP3(sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0),X0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( ~ sP3(X2,X3,k1_enumset1(X1,X1,X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f55,f19])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f89,plain,(
    sK0 != sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK4(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n002.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.49  % (7014)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.17/0.50  % (7013)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.17/0.50  % (7028)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.17/0.50  % (7002)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.17/0.51  % (7002)Refutation not found, incomplete strategy% (7002)------------------------------
% 0.17/0.51  % (7002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (7020)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.17/0.51  % (7013)Refutation not found, incomplete strategy% (7013)------------------------------
% 0.17/0.51  % (7013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (7013)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.51  
% 0.17/0.51  % (7013)Memory used [KB]: 10618
% 0.17/0.51  % (7013)Time elapsed: 0.113 s
% 0.17/0.51  % (7013)------------------------------
% 0.17/0.51  % (7013)------------------------------
% 0.17/0.51  % (7006)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.17/0.51  % (7024)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.17/0.51  % (7009)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.17/0.51  % (7002)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.51  
% 0.17/0.51  % (7002)Memory used [KB]: 1663
% 0.17/0.51  % (7002)Time elapsed: 0.108 s
% 0.17/0.51  % (7002)------------------------------
% 0.17/0.51  % (7002)------------------------------
% 0.17/0.52  % (7020)Refutation found. Thanks to Tanya!
% 0.17/0.52  % SZS status Theorem for theBenchmark
% 0.17/0.52  % (7028)Refutation not found, incomplete strategy% (7028)------------------------------
% 0.17/0.52  % (7028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (7028)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (7028)Memory used [KB]: 6140
% 0.17/0.52  % (7028)Time elapsed: 0.125 s
% 0.17/0.52  % (7028)------------------------------
% 0.17/0.52  % (7028)------------------------------
% 0.17/0.52  % SZS output start Proof for theBenchmark
% 0.17/0.52  fof(f138,plain,(
% 0.17/0.52    $false),
% 0.17/0.52    inference(unit_resulting_resolution,[],[f112,f90,f53])).
% 0.17/0.52  fof(f53,plain,(
% 0.17/0.52    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.17/0.52    inference(equality_resolution,[],[f44])).
% 0.17/0.52  fof(f44,plain,(
% 0.17/0.52    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.17/0.52    inference(definition_unfolding,[],[f22,f35])).
% 0.17/0.52  fof(f35,plain,(
% 0.17/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.17/0.52    inference(cnf_transformation,[],[f2])).
% 0.17/0.52  fof(f2,axiom,(
% 0.17/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.17/0.52  fof(f22,plain,(
% 0.17/0.52    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.17/0.52    inference(cnf_transformation,[],[f1])).
% 0.17/0.52  fof(f1,axiom,(
% 0.17/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.17/0.52  fof(f90,plain,(
% 0.17/0.52    r2_hidden(sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.17/0.52    inference(unit_resulting_resolution,[],[f40,f39,f48])).
% 0.17/0.52  fof(f48,plain,(
% 0.17/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 0.17/0.52    inference(definition_unfolding,[],[f27,f37])).
% 0.17/0.52  fof(f37,plain,(
% 0.17/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.17/0.52    inference(definition_unfolding,[],[f33,f36])).
% 0.17/0.52  fof(f36,plain,(
% 0.17/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f9])).
% 0.17/0.52  fof(f9,axiom,(
% 0.17/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.52  fof(f33,plain,(
% 0.17/0.52    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f8])).
% 0.17/0.52  fof(f8,axiom,(
% 0.17/0.52    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.52  fof(f27,plain,(
% 0.17/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK4(X0,X1),X0)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f14])).
% 0.17/0.52  fof(f14,plain,(
% 0.17/0.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.17/0.52    inference(ennf_transformation,[],[f10])).
% 0.17/0.52  fof(f10,axiom,(
% 0.17/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.17/0.52  fof(f39,plain,(
% 0.17/0.52    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.17/0.52    inference(definition_unfolding,[],[f16,f37,f35,f37])).
% 0.17/0.52  fof(f16,plain,(
% 0.17/0.52    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.17/0.52    inference(cnf_transformation,[],[f13])).
% 0.17/0.52  fof(f13,plain,(
% 0.17/0.52    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.17/0.52    inference(ennf_transformation,[],[f12])).
% 0.17/0.52  fof(f12,negated_conjecture,(
% 0.17/0.52    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.17/0.52    inference(negated_conjecture,[],[f11])).
% 0.17/0.52  fof(f11,conjecture,(
% 0.17/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.17/0.52  fof(f40,plain,(
% 0.17/0.52    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.17/0.52    inference(definition_unfolding,[],[f15,f35,f37])).
% 0.17/0.52  fof(f15,plain,(
% 0.17/0.52    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.17/0.52    inference(cnf_transformation,[],[f13])).
% 0.17/0.52  fof(f112,plain,(
% 0.17/0.52    ( ! [X0] : (~sP3(sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0),X0,k1_enumset1(sK0,sK0,sK0))) )),
% 0.17/0.52    inference(unit_resulting_resolution,[],[f89,f66])).
% 0.17/0.52  fof(f66,plain,(
% 0.17/0.52    ( ! [X2,X3,X1] : (~sP3(X2,X3,k1_enumset1(X1,X1,X1)) | X1 = X2) )),
% 0.17/0.52    inference(resolution,[],[f55,f19])).
% 0.17/0.52  fof(f19,plain,(
% 0.17/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP3(X3,X1,X0)) )),
% 0.17/0.52    inference(cnf_transformation,[],[f1])).
% 0.17/0.52  fof(f55,plain,(
% 0.17/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 0.17/0.52    inference(equality_resolution,[],[f51])).
% 0.17/0.52  fof(f51,plain,(
% 0.17/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.17/0.52    inference(definition_unfolding,[],[f30,f37])).
% 0.17/0.52  fof(f30,plain,(
% 0.17/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.17/0.52    inference(cnf_transformation,[],[f7])).
% 0.17/0.52  fof(f7,axiom,(
% 0.17/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.17/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.17/0.52  fof(f89,plain,(
% 0.17/0.52    sK0 != sK4(k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),sK0)),
% 0.17/0.52    inference(unit_resulting_resolution,[],[f40,f39,f47])).
% 0.17/0.52  fof(f47,plain,(
% 0.17/0.52    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 0.17/0.52    inference(definition_unfolding,[],[f28,f37])).
% 0.17/0.52  fof(f28,plain,(
% 0.17/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK4(X0,X1) != X1) )),
% 0.17/0.52    inference(cnf_transformation,[],[f14])).
% 0.17/0.52  % SZS output end Proof for theBenchmark
% 0.17/0.52  % (7020)------------------------------
% 0.17/0.52  % (7020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (7020)Termination reason: Refutation
% 0.17/0.52  
% 0.17/0.52  % (7020)Memory used [KB]: 1791
% 0.17/0.52  % (7020)Time elapsed: 0.133 s
% 0.17/0.52  % (7020)------------------------------
% 0.17/0.52  % (7020)------------------------------
% 0.17/0.52  % (7029)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.17/0.52  % (7000)Success in time 0.19 s
%------------------------------------------------------------------------------
