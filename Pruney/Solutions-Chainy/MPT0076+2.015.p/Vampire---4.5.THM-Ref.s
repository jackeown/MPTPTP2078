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
% DateTime   : Thu Dec  3 12:30:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  49 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 ( 131 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20,f19])).

fof(f19,plain,(
    ~ r2_hidden(sK2(sK1,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f17,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f17,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f12,f11,f10,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2)
      | ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f10,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f11,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    r2_hidden(sK2(sK1,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f17,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (12008)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.41  % (12008)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f20,f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ~r2_hidden(sK2(sK1,sK1),sK1)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f17,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ~r1_tarski(sK1,sK1)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f12,f11,f10,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | v1_xboole_0(X2) | ~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ~v1_xboole_0(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1))),
% 0.21/0.41    inference(flattening,[],[f5])).
% 0.21/0.41  fof(f5,plain,(
% 0.21/0.41    ? [X0,X1] : ((r1_xboole_0(X1,X0) & r1_tarski(X1,X0)) & ~v1_xboole_0(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f3])).
% 0.21/0.41  fof(f3,conjecture,(
% 0.21/0.41    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    r1_tarski(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    r1_xboole_0(sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    r2_hidden(sK2(sK1,sK1),sK1)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f17,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (12008)------------------------------
% 0.21/0.41  % (12008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (12008)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (12008)Memory used [KB]: 895
% 0.21/0.41  % (12008)Time elapsed: 0.003 s
% 0.21/0.41  % (12008)------------------------------
% 0.21/0.41  % (12008)------------------------------
% 0.21/0.41  % (11991)Success in time 0.06 s
%------------------------------------------------------------------------------
