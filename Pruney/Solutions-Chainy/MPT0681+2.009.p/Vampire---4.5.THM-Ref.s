%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:30 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  64 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 268 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f43])).

fof(f43,plain,(
    r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f38,f23])).

fof(f23,plain,(
    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f38,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0)
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f31,f24])).

fof(f24,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
      ( k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1))
      | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(global_subsumption,[],[f15,f14,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : run_vampire %s %d
% 0.09/0.29  % Computer   : n017.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 18:33:01 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.14/0.33  % (4584)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.33  % (4584)Refutation found. Thanks to Tanya!
% 0.14/0.33  % SZS status Theorem for theBenchmark
% 0.14/0.33  % SZS output start Proof for theBenchmark
% 0.14/0.33  fof(f44,plain,(
% 0.14/0.33    $false),
% 0.14/0.33    inference(global_subsumption,[],[f18,f43])).
% 0.14/0.33  fof(f43,plain,(
% 0.14/0.33    r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.14/0.33    inference(trivial_inequality_removal,[],[f42])).
% 0.14/0.33  fof(f42,plain,(
% 0.14/0.33    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.14/0.33    inference(forward_demodulation,[],[f38,f23])).
% 0.14/0.33  fof(f23,plain,(
% 0.14/0.33    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.14/0.33    inference(resolution,[],[f19,f14])).
% 0.14/0.33  fof(f14,plain,(
% 0.14/0.33    v1_relat_1(sK2)),
% 0.14/0.33    inference(cnf_transformation,[],[f12])).
% 0.14/0.33  fof(f12,plain,(
% 0.14/0.33    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.14/0.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.14/0.33  fof(f11,plain,(
% 0.14/0.33    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.14/0.33    introduced(choice_axiom,[])).
% 0.14/0.33  fof(f7,plain,(
% 0.14/0.33    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.14/0.33    inference(flattening,[],[f6])).
% 0.14/0.33  fof(f6,plain,(
% 0.14/0.33    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.14/0.33    inference(ennf_transformation,[],[f5])).
% 0.14/0.33  fof(f5,negated_conjecture,(
% 0.14/0.33    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.14/0.33    inference(negated_conjecture,[],[f4])).
% 0.14/0.33  fof(f4,conjecture,(
% 0.14/0.33    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.14/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.14/0.33  fof(f19,plain,(
% 0.14/0.33    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 0.14/0.33    inference(cnf_transformation,[],[f8])).
% 0.14/0.33  fof(f8,plain,(
% 0.14/0.33    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.14/0.33    inference(ennf_transformation,[],[f2])).
% 0.14/0.33  fof(f2,axiom,(
% 0.14/0.33    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.14/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.14/0.33  fof(f38,plain,(
% 0.14/0.33    k1_xboole_0 != k9_relat_1(sK2,k1_xboole_0) | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.14/0.33    inference(superposition,[],[f31,f24])).
% 0.14/0.33  fof(f24,plain,(
% 0.14/0.33    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.14/0.33    inference(resolution,[],[f20,f16])).
% 0.14/0.33  fof(f16,plain,(
% 0.14/0.33    r1_xboole_0(sK0,sK1)),
% 0.14/0.33    inference(cnf_transformation,[],[f12])).
% 0.14/0.33  fof(f20,plain,(
% 0.14/0.33    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.14/0.33    inference(cnf_transformation,[],[f13])).
% 0.14/0.33  fof(f13,plain,(
% 0.14/0.33    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.14/0.33    inference(nnf_transformation,[],[f1])).
% 0.14/0.33  fof(f1,axiom,(
% 0.14/0.33    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.14/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.14/0.33  fof(f31,plain,(
% 0.14/0.33    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK2,k3_xboole_0(X0,X1)) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.14/0.33    inference(superposition,[],[f21,f28])).
% 0.14/0.33  fof(f28,plain,(
% 0.14/0.33    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.14/0.33    inference(global_subsumption,[],[f15,f14,f27])).
% 0.14/0.33  fof(f27,plain,(
% 0.14/0.33    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.14/0.33    inference(resolution,[],[f22,f17])).
% 0.14/0.33  fof(f17,plain,(
% 0.14/0.33    v2_funct_1(sK2)),
% 0.14/0.33    inference(cnf_transformation,[],[f12])).
% 0.14/0.33  fof(f22,plain,(
% 0.14/0.33    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.14/0.33    inference(cnf_transformation,[],[f10])).
% 0.14/0.33  fof(f10,plain,(
% 0.14/0.33    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.14/0.33    inference(flattening,[],[f9])).
% 0.14/0.33  fof(f9,plain,(
% 0.14/0.33    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.14/0.33    inference(ennf_transformation,[],[f3])).
% 0.14/0.33  fof(f3,axiom,(
% 0.14/0.33    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.14/0.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.14/0.33  fof(f15,plain,(
% 0.14/0.33    v1_funct_1(sK2)),
% 0.14/0.33    inference(cnf_transformation,[],[f12])).
% 0.14/0.33  fof(f21,plain,(
% 0.14/0.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.14/0.33    inference(cnf_transformation,[],[f13])).
% 0.14/0.33  fof(f18,plain,(
% 0.14/0.33    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.14/0.33    inference(cnf_transformation,[],[f12])).
% 0.14/0.33  % SZS output end Proof for theBenchmark
% 0.14/0.33  % (4584)------------------------------
% 0.14/0.33  % (4584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.33  % (4584)Termination reason: Refutation
% 0.14/0.33  
% 0.14/0.33  % (4584)Memory used [KB]: 6140
% 0.14/0.33  % (4584)Time elapsed: 0.003 s
% 0.14/0.33  % (4584)------------------------------
% 0.14/0.33  % (4584)------------------------------
% 0.14/0.33  % (4585)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.33  % (4586)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.33  % (4571)Success in time 0.035 s
%------------------------------------------------------------------------------
