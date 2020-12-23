%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :   76 ( 159 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(resolution,[],[f115,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f115,plain,(
    ! [X2,X3] : ~ r1_tarski(k2_tarski(k2_tarski(sK0,X2),X3),k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f110,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f110,plain,(
    ! [X0] : ~ r2_hidden(k2_tarski(sK0,X0),k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f103,f89])).

fof(f89,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK2) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

% (20484)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

% (20492)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2)
      | ~ r2_hidden(X0,k2_tarski(k2_tarski(sK0,sK1),sK2)) ) ),
    inference(superposition,[],[f45,f101])).

fof(f101,plain,(
    sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f99,f84])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_tarski(X0,sK2),k2_tarski(k2_tarski(sK0,sK1),sK2))
      | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ) ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,
    ( ~ r2_hidden(sK2,k2_tarski(k2_tarski(sK0,sK1),sK2))
    | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f91,f45])).

fof(f91,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)))
    | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (20470)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (20470)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f115,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(flattening,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_tarski(k2_tarski(k2_tarski(sK0,X2),X3),k2_tarski(k2_tarski(sK0,sK1),sK2))) )),
% 0.22/0.48    inference(resolution,[],[f110,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.48    inference(nnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k2_tarski(sK0,X0),k2_tarski(k2_tarski(sK0,sK1),sK2))) )),
% 0.22/0.48    inference(resolution,[],[f103,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK2)) )),
% 0.22/0.48    inference(resolution,[],[f42,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 0.22/0.48  % (20484)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.48    inference(negated_conjecture,[],[f16])).
% 0.22/0.48  fof(f16,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.22/0.48  % (20492)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(X0,sK2) | ~r2_hidden(X0,k2_tarski(k2_tarski(sK0,sK1),sK2))) )),
% 0.22/0.48    inference(superposition,[],[f45,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.22/0.48    inference(resolution,[],[f99,f84])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k2_tarski(X0,sK2),k2_tarski(k2_tarski(sK0,sK1),sK2)) | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))) )),
% 0.22/0.48    inference(resolution,[],[f98,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k2_tarski(k2_tarski(sK0,sK1),sK2)) | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.22/0.48    inference(resolution,[],[f91,f45])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ~r1_tarski(sK2,k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))) | sK2 = k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.22/0.48    inference(resolution,[],[f48,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK0,sK1),sK2)),sK2)),
% 0.22/0.48    inference(definition_unfolding,[],[f32,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (20470)------------------------------
% 0.22/0.48  % (20470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20470)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (20470)Memory used [KB]: 1791
% 0.22/0.48  % (20470)Time elapsed: 0.088 s
% 0.22/0.48  % (20470)------------------------------
% 0.22/0.48  % (20470)------------------------------
% 0.22/0.49  % (20464)Success in time 0.127 s
%------------------------------------------------------------------------------
