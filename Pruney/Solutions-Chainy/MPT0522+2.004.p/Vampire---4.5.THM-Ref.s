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
% DateTime   : Thu Dec  3 12:48:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 118 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 384 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f47,f47,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X0,X1)
      | r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f47,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f19,f20,f30,f35,f21,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(f21,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (5862)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.45  % (5862)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f23,f47,f47,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r3_xboole_0(X0,X1) | r1_tarski(X0,X1) | r1_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ~r1_tarski(sK1,sK1)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f19,f19,f20,f30,f35,f21,f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.21/0.45    inference(negated_conjecture,[],[f6])).
% 0.21/0.45  fof(f6,conjecture,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),sK2)) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f20,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f20,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0] : (r3_xboole_0(X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0] : r3_xboole_0(X0,X0)),
% 0.21/0.45    inference(rectify,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : r3_xboole_0(X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (5862)------------------------------
% 0.21/0.46  % (5862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5862)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (5862)Memory used [KB]: 5373
% 0.21/0.46  % (5862)Time elapsed: 0.007 s
% 0.21/0.46  % (5862)------------------------------
% 0.21/0.46  % (5862)------------------------------
% 0.21/0.46  % (5842)Success in time 0.101 s
%------------------------------------------------------------------------------
