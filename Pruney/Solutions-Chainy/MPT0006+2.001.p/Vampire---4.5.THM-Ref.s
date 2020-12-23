%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  76 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f18,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f35,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f10,f33])).

fof(f33,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f32,f19])).

fof(f19,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f11,f10])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f32,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f22])).

fof(f22,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f14,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f13,f9])).

fof(f9,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:57:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (31663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (31663)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f35,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    r2_xboole_0(sK0,sK0)),
% 0.20/0.50    inference(backward_demodulation,[],[f10,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    sK0 = sK1),
% 0.20/0.50    inference(subsumption_resolution,[],[f32,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ~r2_xboole_0(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f11,f10])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    sK0 = sK1 | r2_xboole_0(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f17,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f14,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.50    inference(resolution,[],[f13,f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,plain,(
% 0.20/0.50    ? [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f4])).
% 0.20/0.50  fof(f4,conjecture,(
% 0.20/0.50    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    r2_xboole_0(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31663)------------------------------
% 0.20/0.50  % (31663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31663)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31663)Memory used [KB]: 6140
% 0.20/0.50  % (31663)Time elapsed: 0.097 s
% 0.20/0.50  % (31663)------------------------------
% 0.20/0.50  % (31663)------------------------------
% 0.20/0.50  % (31681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (31654)Success in time 0.141 s
%------------------------------------------------------------------------------
