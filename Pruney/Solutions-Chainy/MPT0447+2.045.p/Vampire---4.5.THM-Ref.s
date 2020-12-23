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
% DateTime   : Thu Dec  3 12:47:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 208 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 ( 783 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f647,plain,(
    $false ),
    inference(subsumption_resolution,[],[f646,f512])).

fof(f512,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f392,f57])).

fof(f57,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f34,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f392,plain,(
    ! [X3] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X3)) ),
    inference(superposition,[],[f50,f174])).

fof(f174,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f172,f111])).

fof(f111,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f83,f32])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f80,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f46,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & r1_tarski(X0,sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f172,plain,(
    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f50,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f646,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f630,f33])).

fof(f33,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f630,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f65,f350])).

fof(f350,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f349,f87])).

fof(f87,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_relat_1(sK1))
      | r1_tarski(X3,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f41,f57])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f349,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f224,f142])).

fof(f142,plain,(
    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f140,f98])).

fof(f98,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f47])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK2(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f140,plain,(
    k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f35,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f224,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f118,f89])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f82,f47])).

fof(f118,plain,(
    ! [X6,X4,X5] : r1_tarski(X4,k2_xboole_0(X5,k2_xboole_0(X4,X6))) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k2_xboole_0(X5,X8),X7)
      | r1_tarski(X5,k2_xboole_0(X6,X7)) ) ),
    inference(resolution,[],[f42,f41])).

fof(f65,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),X1)
      | r1_tarski(k3_relat_1(sK0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X1) ) ),
    inference(superposition,[],[f43,f56])).

fof(f56,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f34,f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:49:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (6225)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (6233)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (6219)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (6228)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (6220)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (6227)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (6218)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (6223)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (6215)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (6216)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (6214)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (6222)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (6238)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.57  % (6230)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (6231)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.57  % (6234)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.57  % (6239)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.57  % (6224)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.58  % (6236)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.58  % (6235)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.59  % (6226)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.59  % (6232)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.59  % (6217)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.59  % (6229)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.60  % (6237)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.60  % (6221)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.62  % (6230)Refutation found. Thanks to Tanya!
% 0.22/0.62  % SZS status Theorem for theBenchmark
% 0.22/0.62  % SZS output start Proof for theBenchmark
% 0.22/0.62  fof(f647,plain,(
% 0.22/0.62    $false),
% 0.22/0.62    inference(subsumption_resolution,[],[f646,f512])).
% 0.22/0.62  fof(f512,plain,(
% 0.22/0.62    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.62    inference(superposition,[],[f392,f57])).
% 0.22/0.62  fof(f57,plain,(
% 0.22/0.62    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.62    inference(resolution,[],[f34,f31])).
% 0.22/0.62  fof(f31,plain,(
% 0.22/0.62    v1_relat_1(sK1)),
% 0.22/0.62    inference(cnf_transformation,[],[f25])).
% 0.22/0.62  fof(f25,plain,(
% 0.22/0.62    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).
% 0.22/0.62  fof(f23,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f24,plain,(
% 0.22/0.62    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f13,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.62    inference(flattening,[],[f12])).
% 0.22/0.62  fof(f12,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f11])).
% 0.22/0.62  fof(f11,negated_conjecture,(
% 0.22/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.62    inference(negated_conjecture,[],[f10])).
% 0.22/0.62  fof(f10,conjecture,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.22/0.62  fof(f34,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.62    inference(cnf_transformation,[],[f14])).
% 0.22/0.62  fof(f14,plain,(
% 0.22/0.62    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f7])).
% 0.22/0.62  fof(f7,axiom,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.62  fof(f392,plain,(
% 0.22/0.62    ( ! [X3] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X3))) )),
% 0.22/0.62    inference(superposition,[],[f50,f174])).
% 0.22/0.62  fof(f174,plain,(
% 0.22/0.62    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.62    inference(forward_demodulation,[],[f172,f111])).
% 0.22/0.62  fof(f111,plain,(
% 0.22/0.62    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.62    inference(resolution,[],[f83,f32])).
% 0.22/0.62  fof(f32,plain,(
% 0.22/0.62    r1_tarski(sK0,sK1)),
% 0.22/0.62    inference(cnf_transformation,[],[f25])).
% 0.22/0.62  fof(f83,plain,(
% 0.22/0.62    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f80,f47])).
% 0.22/0.62  fof(f47,plain,(
% 0.22/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.62    inference(equality_resolution,[],[f39])).
% 0.22/0.62  fof(f39,plain,(
% 0.22/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.62    inference(cnf_transformation,[],[f27])).
% 0.22/0.62  fof(f27,plain,(
% 0.22/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.62    inference(flattening,[],[f26])).
% 0.22/0.62  fof(f26,plain,(
% 0.22/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.62    inference(nnf_transformation,[],[f1])).
% 0.22/0.62  fof(f1,axiom,(
% 0.22/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.62  fof(f80,plain,(
% 0.22/0.62    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 0.22/0.62    inference(duplicate_literal_removal,[],[f78])).
% 0.22/0.62  fof(f78,plain,(
% 0.22/0.62    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3)) )),
% 0.22/0.62    inference(resolution,[],[f46,f45])).
% 0.22/0.62  fof(f45,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f29])).
% 0.22/0.62  fof(f29,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f28])).
% 0.22/0.62  fof(f28,plain,(
% 0.22/0.62    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK2(X0,X1,X2)) & r1_tarski(X2,sK2(X0,X1,X2)) & r1_tarski(X0,sK2(X0,X1,X2))))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f22,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.62    inference(flattening,[],[f21])).
% 0.22/0.62  fof(f21,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.62    inference(ennf_transformation,[],[f4])).
% 0.22/0.62  fof(f4,axiom,(
% 0.22/0.62    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.22/0.62  fof(f46,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f29])).
% 0.22/0.62  fof(f172,plain,(
% 0.22/0.62    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.62    inference(resolution,[],[f70,f30])).
% 0.22/0.62  fof(f30,plain,(
% 0.22/0.62    v1_relat_1(sK0)),
% 0.22/0.62    inference(cnf_transformation,[],[f25])).
% 0.22/0.62  fof(f70,plain,(
% 0.22/0.62    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1))) )),
% 0.22/0.62    inference(resolution,[],[f36,f31])).
% 0.22/0.62  fof(f36,plain,(
% 0.22/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f16])).
% 0.22/0.62  fof(f16,plain,(
% 0.22/0.62    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.62    inference(ennf_transformation,[],[f8])).
% 0.22/0.62  fof(f8,axiom,(
% 0.22/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.22/0.62  fof(f50,plain,(
% 0.22/0.62    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 0.22/0.62    inference(resolution,[],[f42,f37])).
% 0.22/0.62  fof(f37,plain,(
% 0.22/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.62    inference(cnf_transformation,[],[f5])).
% 0.22/0.62  fof(f5,axiom,(
% 0.22/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.62  fof(f42,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f18])).
% 0.22/0.62  fof(f18,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.62    inference(ennf_transformation,[],[f3])).
% 0.22/0.62  fof(f3,axiom,(
% 0.22/0.62    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.62  fof(f646,plain,(
% 0.22/0.62    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.62    inference(subsumption_resolution,[],[f630,f33])).
% 0.22/0.62  fof(f33,plain,(
% 0.22/0.62    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.62    inference(cnf_transformation,[],[f25])).
% 0.22/0.62  fof(f630,plain,(
% 0.22/0.62    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.62    inference(resolution,[],[f65,f350])).
% 0.22/0.62  fof(f350,plain,(
% 0.22/0.62    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.22/0.62    inference(resolution,[],[f349,f87])).
% 0.22/0.62  fof(f87,plain,(
% 0.22/0.62    ( ! [X3] : (~r1_tarski(X3,k2_relat_1(sK1)) | r1_tarski(X3,k3_relat_1(sK1))) )),
% 0.22/0.62    inference(superposition,[],[f41,f57])).
% 0.22/0.62  fof(f41,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f17])).
% 0.22/0.62  fof(f17,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.62    inference(ennf_transformation,[],[f2])).
% 0.22/0.62  fof(f2,axiom,(
% 0.22/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.62  fof(f349,plain,(
% 0.22/0.62    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.62    inference(superposition,[],[f224,f142])).
% 0.22/0.62  fof(f142,plain,(
% 0.22/0.62    k2_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 0.22/0.62    inference(forward_demodulation,[],[f140,f98])).
% 0.22/0.62  fof(f98,plain,(
% 0.22/0.62    sK1 = k2_xboole_0(sK1,sK0)),
% 0.22/0.62    inference(resolution,[],[f82,f32])).
% 0.22/0.62  fof(f82,plain,(
% 0.22/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k2_xboole_0(X0,X1) = X0) )),
% 0.22/0.62    inference(subsumption_resolution,[],[f81,f47])).
% 0.22/0.62  fof(f81,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 0.22/0.62    inference(duplicate_literal_removal,[],[f77])).
% 0.22/0.62  fof(f77,plain,(
% 0.22/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 0.22/0.62    inference(resolution,[],[f46,f44])).
% 0.22/0.62  fof(f44,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f29])).
% 0.22/0.62  fof(f140,plain,(
% 0.22/0.62    k2_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0))),
% 0.22/0.62    inference(resolution,[],[f62,f31])).
% 0.22/0.62  fof(f62,plain,(
% 0.22/0.62    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(sK0))) )),
% 0.22/0.62    inference(resolution,[],[f35,f30])).
% 0.22/0.62  fof(f35,plain,(
% 0.22/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f15])).
% 0.22/0.62  fof(f15,plain,(
% 0.22/0.62    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.63    inference(ennf_transformation,[],[f9])).
% 0.22/0.63  fof(f9,axiom,(
% 0.22/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.22/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.22/0.63  fof(f224,plain,(
% 0.22/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.22/0.63    inference(superposition,[],[f118,f89])).
% 0.22/0.63  fof(f89,plain,(
% 0.22/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.63    inference(resolution,[],[f82,f47])).
% 2.18/0.64  fof(f118,plain,(
% 2.18/0.64    ( ! [X6,X4,X5] : (r1_tarski(X4,k2_xboole_0(X5,k2_xboole_0(X4,X6)))) )),
% 2.18/0.64    inference(resolution,[],[f51,f47])).
% 2.18/0.64  fof(f51,plain,(
% 2.18/0.64    ( ! [X6,X8,X7,X5] : (~r1_tarski(k2_xboole_0(X5,X8),X7) | r1_tarski(X5,k2_xboole_0(X6,X7))) )),
% 2.18/0.64    inference(resolution,[],[f42,f41])).
% 2.18/0.64  fof(f65,plain,(
% 2.18/0.64    ( ! [X1] : (~r1_tarski(k2_relat_1(sK0),X1) | r1_tarski(k3_relat_1(sK0),X1) | ~r1_tarski(k1_relat_1(sK0),X1)) )),
% 2.18/0.64    inference(superposition,[],[f43,f56])).
% 2.18/0.64  fof(f56,plain,(
% 2.18/0.64    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 2.18/0.64    inference(resolution,[],[f34,f30])).
% 2.18/0.64  fof(f43,plain,(
% 2.18/0.64    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.18/0.64    inference(cnf_transformation,[],[f20])).
% 2.18/0.64  fof(f20,plain,(
% 2.18/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.18/0.64    inference(flattening,[],[f19])).
% 2.18/0.64  fof(f19,plain,(
% 2.18/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.18/0.64    inference(ennf_transformation,[],[f6])).
% 2.18/0.64  fof(f6,axiom,(
% 2.18/0.64    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.18/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.18/0.64  % SZS output end Proof for theBenchmark
% 2.18/0.64  % (6230)------------------------------
% 2.18/0.64  % (6230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.64  % (6230)Termination reason: Refutation
% 2.18/0.64  
% 2.18/0.64  % (6230)Memory used [KB]: 2046
% 2.18/0.64  % (6230)Time elapsed: 0.214 s
% 2.18/0.64  % (6230)------------------------------
% 2.18/0.64  % (6230)------------------------------
% 2.18/0.65  % (6213)Success in time 0.281 s
%------------------------------------------------------------------------------
