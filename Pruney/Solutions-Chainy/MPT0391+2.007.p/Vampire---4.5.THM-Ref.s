%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  54 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 191 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f17])).

fof(f17,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    & r1_xboole_0(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
      & r1_xboole_0(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f51,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f50,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_setfam_1(X0),sK2)
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f40,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_xboole_0(X1,sK2)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK2),sK0)
      | r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f22,f18])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(X1,X2),X3)
      | ~ r1_tarski(X1,X3)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:26 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.46  % (27381)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.46  % (27391)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (27383)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.46  % (27383)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f51,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => (~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & (r1_xboole_0(X0,X2) & r2_hidden(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f4])).
% 0.20/0.46  fof(f4,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f50,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ~r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(k1_setfam_1(X0),sK2) | ~r2_hidden(sK0,X0)) )),
% 0.20/0.46    inference(resolution,[],[f40,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_xboole_0(X1,sK2)) )),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_xboole_0(X1,sK2) | r1_xboole_0(X1,sK2)) )),
% 0.20/0.46    inference(resolution,[],[f34,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X1] : (~r2_hidden(sK3(X1,sK2),sK0) | r1_xboole_0(X1,sK2)) )),
% 0.20/0.46    inference(resolution,[],[f25,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.46    inference(resolution,[],[f22,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X2,X3,X1] : (r2_hidden(sK3(X1,X2),X3) | ~r1_tarski(X1,X3) | r1_xboole_0(X1,X2)) )),
% 0.20/0.46    inference(resolution,[],[f24,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (27383)------------------------------
% 0.20/0.46  % (27383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27383)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (27383)Memory used [KB]: 5373
% 0.20/0.46  % (27383)Time elapsed: 0.057 s
% 0.20/0.46  % (27383)------------------------------
% 0.20/0.46  % (27383)------------------------------
% 0.20/0.46  % (27375)Success in time 0.107 s
%------------------------------------------------------------------------------
