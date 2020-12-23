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
% DateTime   : Thu Dec  3 12:51:33 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  71 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 231 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f98])).

fof(f98,plain,(
    ~ r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f75,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f75,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(global_subsumption,[],[f21,f72])).

fof(f72,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f49,f42])).

fof(f42,plain,(
    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f36,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(resolution,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_xboole_0(X2,X3))
      | r1_xboole_0(sK0,X2) ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_xboole_0(X1,X2),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f45,plain,(
    ! [X2] :
      ( r1_xboole_0(X2,sK0)
      | ~ r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),X2) ) ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) = k2_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (17917)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.42  % (17917)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f100,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(global_subsumption,[],[f20,f98])).
% 0.13/0.42  fof(f98,plain,(
% 0.13/0.42    ~r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.13/0.42    inference(resolution,[],[f75,f28])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.13/0.42  fof(f75,plain,(
% 0.13/0.42    ~r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.13/0.42    inference(global_subsumption,[],[f21,f72])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    ~r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | r1_xboole_0(sK0,sK1)),
% 0.13/0.42    inference(superposition,[],[f49,f42])).
% 0.13/0.42  fof(f42,plain,(
% 0.13/0.42    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.13/0.42    inference(resolution,[],[f36,f19])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    v1_relat_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f17])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16,f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f8])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,negated_conjecture,(
% 0.13/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.13/0.42    inference(negated_conjecture,[],[f6])).
% 0.13/0.42  fof(f6,conjecture,(
% 0.13/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_relat_1(X0) | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.13/0.42    inference(resolution,[],[f22,f23])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.13/0.42  fof(f49,plain,(
% 0.13/0.42    ( ! [X2,X3] : (~r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k2_xboole_0(X2,X3)) | r1_xboole_0(sK0,X2)) )),
% 0.13/0.42    inference(resolution,[],[f45,f32])).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_xboole_0(X1,X2),X0) | r1_xboole_0(X0,X1)) )),
% 0.13/0.42    inference(resolution,[],[f26,f24])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f1])).
% 0.13/0.43  fof(f1,axiom,(
% 0.13/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.13/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.13/0.43  fof(f26,plain,(
% 0.13/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.13/0.43    inference(cnf_transformation,[],[f13])).
% 0.13/0.43  fof(f13,plain,(
% 0.13/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.13/0.43    inference(ennf_transformation,[],[f3])).
% 0.13/0.43  fof(f3,axiom,(
% 0.13/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.13/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.13/0.43  fof(f45,plain,(
% 0.13/0.43    ( ! [X2] : (r1_xboole_0(X2,sK0) | ~r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),X2)) )),
% 0.13/0.43    inference(superposition,[],[f32,f41])).
% 0.13/0.43  fof(f41,plain,(
% 0.13/0.43    k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) = k2_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.13/0.43    inference(resolution,[],[f36,f18])).
% 0.13/0.43  fof(f18,plain,(
% 0.13/0.43    v1_relat_1(sK0)),
% 0.13/0.43    inference(cnf_transformation,[],[f17])).
% 0.13/0.43  fof(f21,plain,(
% 0.13/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.13/0.43    inference(cnf_transformation,[],[f17])).
% 0.13/0.43  fof(f20,plain,(
% 0.13/0.43    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.13/0.43    inference(cnf_transformation,[],[f17])).
% 0.13/0.43  % SZS output end Proof for theBenchmark
% 0.13/0.43  % (17917)------------------------------
% 0.13/0.43  % (17917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.43  % (17917)Termination reason: Refutation
% 0.13/0.43  
% 0.13/0.43  % (17917)Memory used [KB]: 6140
% 0.13/0.43  % (17917)Time elapsed: 0.007 s
% 0.13/0.43  % (17917)------------------------------
% 0.13/0.43  % (17917)------------------------------
% 0.21/0.43  % (17912)Success in time 0.063 s
%------------------------------------------------------------------------------
