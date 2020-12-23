%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:55 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   33 (  59 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 197 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(resolution,[],[f239,f19])).

fof(f19,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).

fof(f239,plain,(
    ! [X0] : r1_tarski(k5_relat_1(sK1,k8_relat_1(X0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f108,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X0,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X0,sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X1] : v1_relat_1(k8_relat_1(X1,sK2)) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2))
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(k8_relat_1(X1,sK2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f43,f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2))
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k8_relat_1(X1,sK2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f31,plain,(
    ! [X1] : r1_tarski(k8_relat_1(X1,sK2),sK2) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.37  ipcrm: permission denied for id (1232437250)
% 0.19/0.37  ipcrm: permission denied for id (1232470020)
% 0.19/0.37  ipcrm: permission denied for id (1232502792)
% 0.19/0.38  ipcrm: permission denied for id (1232535568)
% 0.19/0.41  ipcrm: permission denied for id (1232601124)
% 0.19/0.41  ipcrm: permission denied for id (1232633899)
% 0.19/0.42  ipcrm: permission denied for id (1232666674)
% 0.20/0.45  ipcrm: permission denied for id (1232765005)
% 0.20/0.47  ipcrm: permission denied for id (1232830557)
% 0.20/0.49  ipcrm: permission denied for id (1232863341)
% 0.80/0.63  % (8281)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.80/0.64  % (8281)Refutation found. Thanks to Tanya!
% 0.80/0.64  % SZS status Theorem for theBenchmark
% 0.80/0.64  % (8290)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.80/0.64  % SZS output start Proof for theBenchmark
% 0.80/0.64  fof(f453,plain,(
% 0.80/0.64    $false),
% 0.80/0.64    inference(resolution,[],[f239,f19])).
% 0.80/0.64  fof(f19,plain,(
% 0.80/0.64    ~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))),
% 0.80/0.64    inference(cnf_transformation,[],[f14])).
% 0.80/0.64  fof(f14,plain,(
% 0.80/0.64    (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.80/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.80/0.64  fof(f12,plain,(
% 0.80/0.64    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.80/0.64    introduced(choice_axiom,[])).
% 0.80/0.64  fof(f13,plain,(
% 0.80/0.64    ? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.80/0.64    introduced(choice_axiom,[])).
% 0.80/0.64  fof(f7,plain,(
% 0.80/0.64    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.80/0.64    inference(ennf_transformation,[],[f6])).
% 0.80/0.64  fof(f6,negated_conjecture,(
% 0.80/0.64    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.80/0.64    inference(negated_conjecture,[],[f5])).
% 0.80/0.64  fof(f5,conjecture,(
% 0.80/0.64    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).
% 0.80/0.64  fof(f239,plain,(
% 0.80/0.64    ( ! [X0] : (r1_tarski(k5_relat_1(sK1,k8_relat_1(X0,sK2)),k5_relat_1(sK1,sK2))) )),
% 0.80/0.64    inference(resolution,[],[f108,f17])).
% 0.80/0.64  fof(f17,plain,(
% 0.80/0.64    v1_relat_1(sK1)),
% 0.80/0.64    inference(cnf_transformation,[],[f14])).
% 0.80/0.64  fof(f108,plain,(
% 0.80/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X0,sK2))) )),
% 0.80/0.64    inference(duplicate_literal_removal,[],[f103])).
% 0.80/0.64  fof(f103,plain,(
% 0.80/0.64    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X0,sK2)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(resolution,[],[f46,f26])).
% 0.80/0.64  fof(f26,plain,(
% 0.80/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.80/0.64    inference(equality_resolution,[],[f24])).
% 0.80/0.64  fof(f24,plain,(
% 0.80/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.80/0.64    inference(cnf_transformation,[],[f16])).
% 0.80/0.64  fof(f16,plain,(
% 0.80/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.80/0.64    inference(flattening,[],[f15])).
% 0.80/0.64  fof(f15,plain,(
% 0.80/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.80/0.64    inference(nnf_transformation,[],[f1])).
% 0.80/0.64  fof(f1,axiom,(
% 0.80/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.80/0.64  fof(f46,plain,(
% 0.80/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(subsumption_resolution,[],[f45,f29])).
% 0.80/0.64  fof(f29,plain,(
% 0.80/0.64    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK2))) )),
% 0.80/0.64    inference(resolution,[],[f21,f18])).
% 0.80/0.64  fof(f18,plain,(
% 0.80/0.64    v1_relat_1(sK2)),
% 0.80/0.64    inference(cnf_transformation,[],[f14])).
% 0.80/0.64  fof(f21,plain,(
% 0.80/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.80/0.64    inference(cnf_transformation,[],[f10])).
% 0.80/0.64  fof(f10,plain,(
% 0.80/0.64    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.80/0.64    inference(ennf_transformation,[],[f2])).
% 0.80/0.64  fof(f2,axiom,(
% 0.80/0.64    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.80/0.64  fof(f45,plain,(
% 0.80/0.64    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2)) | ~r1_tarski(X0,X2) | ~v1_relat_1(k8_relat_1(X1,sK2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(subsumption_resolution,[],[f43,f18])).
% 0.80/0.64  fof(f43,plain,(
% 0.80/0.64    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,k8_relat_1(X1,sK2)),k5_relat_1(X2,sK2)) | ~r1_tarski(X0,X2) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(X1,sK2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(resolution,[],[f31,f20])).
% 0.80/0.64  fof(f20,plain,(
% 0.80/0.64    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f9])).
% 0.80/0.64  fof(f9,plain,(
% 0.80/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.80/0.64    inference(flattening,[],[f8])).
% 0.80/0.64  fof(f8,plain,(
% 0.80/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.80/0.64    inference(ennf_transformation,[],[f4])).
% 0.80/0.64  fof(f4,axiom,(
% 0.80/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.80/0.64  fof(f31,plain,(
% 0.80/0.64    ( ! [X1] : (r1_tarski(k8_relat_1(X1,sK2),sK2)) )),
% 0.80/0.64    inference(resolution,[],[f22,f18])).
% 0.80/0.64  fof(f22,plain,(
% 0.80/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f11])).
% 0.80/0.64  fof(f11,plain,(
% 0.80/0.64    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.80/0.64    inference(ennf_transformation,[],[f3])).
% 0.80/0.64  fof(f3,axiom,(
% 0.80/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.80/0.64  % SZS output end Proof for theBenchmark
% 0.80/0.64  % (8281)------------------------------
% 0.80/0.64  % (8281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.64  % (8281)Termination reason: Refutation
% 0.80/0.64  
% 0.80/0.64  % (8281)Memory used [KB]: 11001
% 0.80/0.64  % (8281)Time elapsed: 0.062 s
% 0.80/0.64  % (8281)------------------------------
% 0.80/0.64  % (8281)------------------------------
% 0.80/0.64  % (8137)Success in time 0.284 s
%------------------------------------------------------------------------------
