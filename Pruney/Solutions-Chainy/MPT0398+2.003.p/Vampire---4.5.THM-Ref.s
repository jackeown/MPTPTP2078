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
% DateTime   : Thu Dec  3 12:46:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(resolution,[],[f22,f13])).

fof(f13,plain,(
    ~ r1_setfam_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : ~ r1_setfam_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).

fof(f22,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] : r2_hidden(X2,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] : ~ r2_hidden(X2,X0)
     => r1_setfam_1(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f21,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f20,f14])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f16,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (16926)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (16932)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (16934)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (16926)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(resolution,[],[f22,f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ~r1_setfam_1(k1_xboole_0,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0] : ~r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0] : r1_setfam_1(k1_xboole_0,X0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_setfam_1)).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0] : (r1_setfam_1(k1_xboole_0,X0)) )),
% 0.20/0.41    inference(resolution,[],[f21,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r2_hidden(sK2(X0),X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : r2_hidden(X2,X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : ~r2_hidden(X2,X0) => r1_setfam_1(X0,X1))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.20/0.41    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.41    inference(subsumption_resolution,[],[f20,f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(superposition,[],[f16,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    inference(rectify,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (16926)------------------------------
% 0.20/0.41  % (16926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (16926)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (16926)Memory used [KB]: 10490
% 0.20/0.41  % (16926)Time elapsed: 0.005 s
% 0.20/0.41  % (16926)------------------------------
% 0.20/0.41  % (16926)------------------------------
% 0.20/0.42  % (16925)Success in time 0.062 s
%------------------------------------------------------------------------------
