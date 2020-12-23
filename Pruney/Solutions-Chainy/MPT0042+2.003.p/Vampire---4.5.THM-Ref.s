%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  42 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(subsumption_resolution,[],[f165,f13])).

fof(f13,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f165,plain,(
    r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))
    | r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f148,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f148,plain,(
    ! [X33] :
      ( r2_hidden(sK4(k4_xboole_0(sK0,sK3),X33),k4_xboole_0(sK1,sK2))
      | r1_tarski(k4_xboole_0(sK0,sK3),X33) ) ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(X7,sK3),k4_xboole_0(X7,sK2)) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(sK1,X1),X3)
      | r2_hidden(sK4(k4_xboole_0(sK0,X1),X2),X3)
      | r1_tarski(k4_xboole_0(sK0,X1),X2) ) ),
    inference(resolution,[],[f49,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(k4_xboole_0(sK0,X2),X3),k4_xboole_0(sK1,X2))
      | r1_tarski(k4_xboole_0(sK0,X2),X3) ) ),
    inference(resolution,[],[f21,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f17,f11])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f14,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (2135)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.44  % (2135)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f165,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) | r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.21/0.44    inference(resolution,[],[f148,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ( ! [X33] : (r2_hidden(sK4(k4_xboole_0(sK0,sK3),X33),k4_xboole_0(sK1,sK2)) | r1_tarski(k4_xboole_0(sK0,sK3),X33)) )),
% 0.21/0.44    inference(resolution,[],[f76,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X7] : (r1_tarski(k4_xboole_0(X7,sK3),k4_xboole_0(X7,sK2))) )),
% 0.21/0.44    inference(resolution,[],[f18,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    r1_tarski(sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ( ! [X2,X3,X1] : (~r1_tarski(k4_xboole_0(sK1,X1),X3) | r2_hidden(sK4(k4_xboole_0(sK0,X1),X2),X3) | r1_tarski(k4_xboole_0(sK0,X1),X2)) )),
% 0.21/0.44    inference(resolution,[],[f49,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r2_hidden(sK4(k4_xboole_0(sK0,X2),X3),k4_xboole_0(sK1,X2)) | r1_tarski(k4_xboole_0(sK0,X2),X3)) )),
% 0.21/0.44    inference(resolution,[],[f21,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,X0))) )),
% 0.21/0.44    inference(resolution,[],[f17,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(resolution,[],[f14,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (2135)------------------------------
% 0.21/0.44  % (2135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (2135)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (2135)Memory used [KB]: 5373
% 0.21/0.44  % (2135)Time elapsed: 0.007 s
% 0.21/0.44  % (2135)------------------------------
% 0.21/0.44  % (2135)------------------------------
% 0.21/0.44  % (2125)Success in time 0.086 s
%------------------------------------------------------------------------------
