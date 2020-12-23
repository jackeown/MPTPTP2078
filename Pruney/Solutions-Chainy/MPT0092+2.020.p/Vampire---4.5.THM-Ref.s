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
% DateTime   : Thu Dec  3 12:31:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  59 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f21,f15,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK1)
      | r1_xboole_0(X0,sK0) ) ),
    inference(superposition,[],[f19,f27])).

fof(f27,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f21,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f14,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.40  % (2729)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.40  % (2729)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f36,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(unit_resulting_resolution,[],[f21,f15,f33])).
% 0.20/0.40  fof(f33,plain,(
% 0.20/0.40    ( ! [X0] : (~r1_xboole_0(X0,sK1) | r1_xboole_0(X0,sK0)) )),
% 0.20/0.40    inference(superposition,[],[f19,f27])).
% 0.20/0.40  fof(f27,plain,(
% 0.20/0.40    sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.40    inference(unit_resulting_resolution,[],[f13,f16])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.40    inference(cnf_transformation,[],[f8])).
% 0.20/0.40  fof(f8,plain,(
% 0.20/0.40    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    r1_tarski(sK0,sK1)),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f6])).
% 0.20/0.40  fof(f6,negated_conjecture,(
% 0.20/0.40    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.40    inference(negated_conjecture,[],[f5])).
% 0.20/0.40  fof(f5,conjecture,(
% 0.20/0.40    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f10])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.40    inference(ennf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.40  fof(f21,plain,(
% 0.20/0.40    ~r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)),
% 0.20/0.40    inference(unit_resulting_resolution,[],[f14,f17])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f9])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.20/0.40    inference(cnf_transformation,[],[f12])).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (2729)------------------------------
% 0.20/0.40  % (2729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (2729)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (2729)Memory used [KB]: 6012
% 0.20/0.40  % (2729)Time elapsed: 0.028 s
% 0.20/0.40  % (2729)------------------------------
% 0.20/0.40  % (2729)------------------------------
% 0.20/0.40  % (2726)Success in time 0.06 s
%------------------------------------------------------------------------------
