%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f32,f35,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f15,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f35,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f11,f25,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f25,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f10,plain,(
    r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,X1)
      & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_hidden(X0,X1)
          & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f11,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X3] : sP3(X3,X3,X0) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (11877)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.49  % (11885)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.49  % (11877)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f32,f35,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_enumset1(X0,X0,X1)) | ~sP3(X3,X1,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.19/0.49    inference(definition_unfolding,[],[f15,f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f11,f25,f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,plain,(
% 0.19/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.49    inference(rectify,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.19/0.49    inference(definition_unfolding,[],[f10,f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.49    inference(definition_unfolding,[],[f22,f23])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,plain,(
% 0.19/0.49    ? [X0,X1] : (r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.49    inference(negated_conjecture,[],[f5])).
% 0.19/0.49  fof(f5,conjecture,(
% 0.19/0.49    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    r2_hidden(sK0,sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0,X3] : (sP3(X3,X3,X0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ( ! [X0,X3,X1] : (X1 != X3 | sP3(X3,X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (11877)------------------------------
% 0.19/0.49  % (11877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (11877)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (11877)Memory used [KB]: 1663
% 0.19/0.49  % (11877)Time elapsed: 0.082 s
% 0.19/0.49  % (11877)------------------------------
% 0.19/0.49  % (11877)------------------------------
% 0.19/0.49  % (11857)Success in time 0.14 s
%------------------------------------------------------------------------------
