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
% DateTime   : Thu Dec  3 12:46:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  91 expanded)
%              Number of leaves         :    3 (  19 expanded)
%              Depth                    :   16
%              Number of atoms          :   98 ( 264 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(subsumption_resolution,[],[f391,f11])).

fof(f11,plain,(
    ~ r1_setfam_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f391,plain,(
    r1_setfam_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,
    ( r1_setfam_1(sK0,sK2)
    | r1_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f389,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),sK2)
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f46,f10])).

fof(f10,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X3] :
      ( ~ r1_setfam_1(sK1,X3)
      | r2_hidden(sK5(X3,sK5(sK1,sK4(sK0,X2))),X3)
      | r1_setfam_1(sK0,X2) ) ),
    inference(resolution,[],[f42,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(sK5(X1,X2),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK4(sK0,X0)),sK1)
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f27,f9])).

fof(f9,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_setfam_1(X4,X3)
      | r2_hidden(sK5(X3,sK4(X4,X5)),X3)
      | r1_setfam_1(X4,X5) ) ),
    inference(resolution,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f389,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),X0)
      | r1_setfam_1(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,(
    ! [X0] :
      ( r1_setfam_1(sK0,X0)
      | ~ r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),X0)
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f385,f15])).

fof(f15,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X3)
      | ~ r2_hidden(X3,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f385,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0))))
      | r1_setfam_1(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0))))
      | r1_setfam_1(sK0,X0)
      | r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) ) ),
    inference(resolution,[],[f366,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
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

fof(f366,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK4(sK0,X0),X1),sK5(sK2,sK5(sK1,sK4(sK0,X0))))
      | r1_tarski(sK4(sK0,X0),X1)
      | r1_setfam_1(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(sK0,X0),X1)
      | r2_hidden(sK3(sK4(sK0,X0),X1),sK5(sK2,sK5(sK1,sK4(sK0,X0))))
      | r1_setfam_1(sK0,X0)
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f204,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r1_tarski(sK5(sK1,sK4(sK0,X0)),sK5(sK2,sK5(sK1,sK4(sK0,X0))))
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f45,f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(sK1,X1)
      | r1_tarski(sK5(sK1,sK4(sK0,X0)),sK5(X1,sK5(sK1,sK4(sK0,X0))))
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f42,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK5(X1,X2))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f204,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_tarski(sK5(sK1,sK4(sK0,X7)),X9)
      | r1_tarski(sK4(sK0,X7),X8)
      | r2_hidden(sK3(sK4(sK0,X7),X8),X9)
      | r1_setfam_1(sK0,X7) ) ),
    inference(resolution,[],[f87,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK3(sK4(sK0,X3),X4),sK5(sK1,sK4(sK0,X3)))
      | r1_setfam_1(sK0,X3)
      | r1_tarski(sK4(sK0,X3),X4) ) ),
    inference(resolution,[],[f82,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(sK4(sK0,X0),sK5(sK1,sK4(sK0,X0)))
      | r1_setfam_1(sK0,X0) ) ),
    inference(resolution,[],[f29,f9])).

fof(f29,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_setfam_1(X3,X5)
      | r1_tarski(sK4(X3,X4),sK5(X5,sK4(X3,X4)))
      | r1_setfam_1(X3,X4) ) ),
    inference(resolution,[],[f17,f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n023.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:13:21 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.22/0.48  % (5005)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (5005)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (5012)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f392,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f391,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ~r1_setfam_1(sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & (r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.22/0.49    inference(negated_conjecture,[],[f3])).
% 0.22/0.49  fof(f3,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    r1_setfam_1(sK0,sK2)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f390])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    r1_setfam_1(sK0,sK2) | r1_setfam_1(sK0,sK2)),
% 0.22/0.49    inference(resolution,[],[f389,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),sK2) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f46,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    r1_setfam_1(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r1_setfam_1(sK1,X3) | r2_hidden(sK5(X3,sK5(sK1,sK4(sK0,X2))),X3) | r1_setfam_1(sK0,X2)) )),
% 0.22/0.49    inference(resolution,[],[f42,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(sK5(X1,X2),X1) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK5(sK1,sK4(sK0,X0)),sK1) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f27,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    r1_setfam_1(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~r1_setfam_1(X4,X3) | r2_hidden(sK5(X3,sK4(X4,X5)),X3) | r1_setfam_1(X4,X5)) )),
% 0.22/0.49    inference(resolution,[],[f16,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),X0) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f386])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    ( ! [X0] : (r1_setfam_1(sK0,X0) | ~r2_hidden(sK5(sK2,sK5(sK1,sK4(sK0,X0))),X0) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f385,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X1) | r1_setfam_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f381])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) | r1_setfam_1(sK0,X0) | r1_tarski(sK4(sK0,X0),sK5(sK2,sK5(sK1,sK4(sK0,X0))))) )),
% 0.22/0.49    inference(resolution,[],[f366,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.49  fof(f366,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(sK4(sK0,X0),X1),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) | r1_tarski(sK4(sK0,X0),X1) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f362])).
% 0.22/0.49  fof(f362,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(sK4(sK0,X0),X1) | r2_hidden(sK3(sK4(sK0,X0),X1),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) | r1_setfam_1(sK0,X0) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f204,f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(sK5(sK1,sK4(sK0,X0)),sK5(sK2,sK5(sK1,sK4(sK0,X0)))) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f45,f10])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_setfam_1(sK1,X1) | r1_tarski(sK5(sK1,sK4(sK0,X0)),sK5(X1,sK5(sK1,sK4(sK0,X0)))) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f42,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,sK5(X1,X2)) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    ( ! [X8,X7,X9] : (~r1_tarski(sK5(sK1,sK4(sK0,X7)),X9) | r1_tarski(sK4(sK0,X7),X8) | r2_hidden(sK3(sK4(sK0,X7),X8),X9) | r1_setfam_1(sK0,X7)) )),
% 0.22/0.49    inference(resolution,[],[f87,f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X4,X3] : (r2_hidden(sK3(sK4(sK0,X3),X4),sK5(sK1,sK4(sK0,X3))) | r1_setfam_1(sK0,X3) | r1_tarski(sK4(sK0,X3),X4)) )),
% 0.22/0.49    inference(resolution,[],[f82,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f12,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(sK4(sK0,X0),sK5(sK1,sK4(sK0,X0))) | r1_setfam_1(sK0,X0)) )),
% 0.22/0.49    inference(resolution,[],[f29,f9])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (~r1_setfam_1(X3,X5) | r1_tarski(sK4(X3,X4),sK5(X5,sK4(X3,X4))) | r1_setfam_1(X3,X4)) )),
% 0.22/0.49    inference(resolution,[],[f17,f18])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (5005)------------------------------
% 0.22/0.49  % (5005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5005)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (5005)Memory used [KB]: 5500
% 0.22/0.49  % (5005)Time elapsed: 0.051 s
% 0.22/0.49  % (5005)------------------------------
% 0.22/0.49  % (5005)------------------------------
% 0.22/0.49  % (4995)Success in time 0.113 s
%------------------------------------------------------------------------------
