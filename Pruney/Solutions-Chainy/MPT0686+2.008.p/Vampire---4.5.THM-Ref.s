%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:37 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  62 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 212 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f43])).

fof(f43,plain,(
    r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f38,f23])).

fof(f23,plain,(
    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2,X1] :
        ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
        & r1_xboole_0(X1,X2) )
   => ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f38,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f31,f24])).

fof(f24,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1))
      | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ) ),
    inference(superposition,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) ),
    inference(global_subsumption,[],[f15,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (29758)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.43  % (29755)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.43  % (29755)Refutation found. Thanks to Tanya!
% 0.14/0.43  % SZS status Theorem for theBenchmark
% 0.14/0.43  % SZS output start Proof for theBenchmark
% 0.14/0.43  fof(f44,plain,(
% 0.14/0.43    $false),
% 0.14/0.43    inference(global_subsumption,[],[f18,f43])).
% 0.14/0.43  fof(f43,plain,(
% 0.14/0.43    r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.14/0.43    inference(trivial_inequality_removal,[],[f42])).
% 0.14/0.43  fof(f42,plain,(
% 0.14/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.14/0.43    inference(forward_demodulation,[],[f38,f23])).
% 0.14/0.43  fof(f23,plain,(
% 0.14/0.43    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.14/0.43    inference(resolution,[],[f19,f15])).
% 0.14/0.43  fof(f15,plain,(
% 0.14/0.43    v1_relat_1(sK0)),
% 0.14/0.43    inference(cnf_transformation,[],[f13])).
% 0.14/0.43  fof(f13,plain,(
% 0.14/0.43    (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.14/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12,f11])).
% 0.14/0.43  fof(f11,plain,(
% 0.14/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.14/0.43    introduced(choice_axiom,[])).
% 0.14/0.43  fof(f12,plain,(
% 0.14/0.43    ? [X2,X1] : (~r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2)) & r1_xboole_0(X1,X2)) => (~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) & r1_xboole_0(sK1,sK2))),
% 0.14/0.43    introduced(choice_axiom,[])).
% 0.14/0.43  fof(f7,plain,(
% 0.14/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.14/0.43    inference(flattening,[],[f6])).
% 0.14/0.43  fof(f6,plain,(
% 0.14/0.43    ? [X0] : (? [X1,X2] : (~r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) & r1_xboole_0(X1,X2)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.14/0.43    inference(ennf_transformation,[],[f5])).
% 0.14/0.43  fof(f5,negated_conjecture,(
% 0.14/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.14/0.43    inference(negated_conjecture,[],[f4])).
% 0.14/0.43  fof(f4,conjecture,(
% 0.14/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_xboole_0(X1,X2) => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).
% 0.14/0.43  fof(f19,plain,(
% 0.14/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f8])).
% 0.14/0.43  fof(f8,plain,(
% 0.14/0.43    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.14/0.43    inference(ennf_transformation,[],[f2])).
% 0.14/0.43  fof(f2,axiom,(
% 0.14/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.14/0.43  fof(f38,plain,(
% 0.14/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.14/0.43    inference(superposition,[],[f31,f24])).
% 0.14/0.43  fof(f24,plain,(
% 0.14/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.14/0.43    inference(resolution,[],[f20,f17])).
% 0.14/0.43  fof(f17,plain,(
% 0.14/0.43    r1_xboole_0(sK1,sK2)),
% 0.14/0.43    inference(cnf_transformation,[],[f13])).
% 0.14/0.43  fof(f20,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.14/0.43    inference(cnf_transformation,[],[f14])).
% 0.14/0.43  fof(f14,plain,(
% 0.14/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.14/0.43    inference(nnf_transformation,[],[f1])).
% 0.14/0.43  fof(f1,axiom,(
% 0.14/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.14/0.43  fof(f31,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(sK0,k3_xboole_0(X0,X1)) | r1_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) )),
% 0.14/0.43    inference(superposition,[],[f21,f28])).
% 0.14/0.43  fof(f28,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))) )),
% 0.14/0.43    inference(global_subsumption,[],[f15,f27])).
% 0.14/0.43  fof(f27,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) )),
% 0.14/0.43    inference(resolution,[],[f22,f16])).
% 0.14/0.43  fof(f16,plain,(
% 0.14/0.43    v1_funct_1(sK0)),
% 0.14/0.43    inference(cnf_transformation,[],[f13])).
% 0.14/0.43  fof(f22,plain,(
% 0.14/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f10])).
% 0.14/0.43  fof(f10,plain,(
% 0.14/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.14/0.43    inference(flattening,[],[f9])).
% 0.14/0.43  fof(f9,plain,(
% 0.14/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.14/0.43    inference(ennf_transformation,[],[f3])).
% 0.14/0.43  fof(f3,axiom,(
% 0.14/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).
% 0.14/0.43  fof(f21,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f14])).
% 0.14/0.43  fof(f18,plain,(
% 0.14/0.43    ~r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))),
% 0.14/0.43    inference(cnf_transformation,[],[f13])).
% 0.14/0.43  % SZS output end Proof for theBenchmark
% 0.14/0.43  % (29755)------------------------------
% 0.14/0.43  % (29755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.43  % (29755)Termination reason: Refutation
% 0.14/0.43  
% 0.14/0.43  % (29755)Memory used [KB]: 6140
% 0.14/0.43  % (29755)Time elapsed: 0.005 s
% 0.14/0.43  % (29755)------------------------------
% 0.14/0.43  % (29755)------------------------------
% 0.21/0.43  % (29750)Success in time 0.065 s
%------------------------------------------------------------------------------
