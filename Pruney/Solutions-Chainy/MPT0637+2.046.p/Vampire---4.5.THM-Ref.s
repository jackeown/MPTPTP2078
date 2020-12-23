%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:28 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 160 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 268 expanded)
%              Number of equality atoms :   52 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f106,f937,f126])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3))
      | k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f113,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f113,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f75,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f75,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

% (15401)Refutation not found, incomplete strategy% (15401)------------------------------
% (15401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15401)Termination reason: Refutation not found, incomplete strategy

% (15401)Memory used [KB]: 10618
% (15401)Time elapsed: 0.177 s
% (15401)------------------------------
% (15401)------------------------------
fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

% (15385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f59,f72])).

fof(f72,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f937,plain,(
    ! [X6,X5] : r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(forward_demodulation,[],[f925,f76])).

fof(f925,plain,(
    ! [X6,X5] : r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6))) ),
    inference(superposition,[],[f256,f105])).

fof(f105,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f72,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f62,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f39,f36])).

% (15411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f256,plain,(
    ! [X6,X7,X5] : r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(X5,X6)),X7),k7_relat_1(k6_relat_1(X5),X7)) ),
    inference(superposition,[],[f176,f109])).

fof(f109,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1) ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f80,f72])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f79,f37])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f51,f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f176,plain,(
    ! [X14,X15,X16] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X16),X14),X15),k7_relat_1(k6_relat_1(X14),X15)) ),
    inference(backward_demodulation,[],[f98,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f172,f72])).

fof(f172,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f170,f96])).

fof(f96,plain,(
    ! [X10,X8,X9] : k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X10) = k5_relat_1(k6_relat_1(X10),k7_relat_1(k6_relat_1(X8),X9)) ),
    inference(resolution,[],[f78,f47])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f77,f72])).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f61,f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f170,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f117,f36])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f115,f72])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f36])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f98,plain,(
    ! [X14,X15,X16] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(X16)),k7_relat_1(k6_relat_1(X14),X15)) ),
    inference(resolution,[],[f78,f49])).

fof(f106,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f35,f72])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

% (15411)Refutation not found, incomplete strategy% (15411)------------------------------
% (15411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15411)Termination reason: Refutation not found, incomplete strategy

% (15410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (15411)Memory used [KB]: 6140
% (15411)Time elapsed: 0.173 s
% (15411)------------------------------
% (15411)------------------------------
fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n019.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.31  % CPULimit   : 60
% 0.15/0.31  % WCLimit    : 600
% 0.15/0.31  % DateTime   : Tue Dec  1 18:33:07 EST 2020
% 0.15/0.31  % CPUTime    : 
% 0.18/0.47  % (15392)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.48  % (15400)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.49  % (15388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.51  % (15404)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.18/0.51  % (15393)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.18/0.52  % (15405)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.53  % (15414)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.53  % (15414)Refutation not found, incomplete strategy% (15414)------------------------------
% 0.18/0.53  % (15414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (15414)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (15414)Memory used [KB]: 10618
% 0.18/0.53  % (15414)Time elapsed: 0.149 s
% 0.18/0.53  % (15414)------------------------------
% 0.18/0.53  % (15414)------------------------------
% 0.18/0.53  % (15389)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.54  % (15394)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.57/0.54  % (15397)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.54  % (15387)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.54  % (15390)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.54  % (15407)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.54  % (15397)Refutation not found, incomplete strategy% (15397)------------------------------
% 1.57/0.54  % (15397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.54  % (15397)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.54  
% 1.57/0.54  % (15397)Memory used [KB]: 10618
% 1.57/0.54  % (15397)Time elapsed: 0.157 s
% 1.57/0.54  % (15397)------------------------------
% 1.57/0.54  % (15397)------------------------------
% 1.57/0.54  % (15386)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.57/0.54  % (15386)Refutation not found, incomplete strategy% (15386)------------------------------
% 1.57/0.54  % (15386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.54  % (15386)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.54  
% 1.57/0.54  % (15386)Memory used [KB]: 1663
% 1.57/0.54  % (15386)Time elapsed: 0.158 s
% 1.57/0.54  % (15386)------------------------------
% 1.57/0.54  % (15386)------------------------------
% 1.57/0.54  % (15399)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.57/0.54  % (15396)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.57/0.54  % (15399)Refutation not found, incomplete strategy% (15399)------------------------------
% 1.57/0.54  % (15399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.54  % (15399)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.54  
% 1.57/0.54  % (15399)Memory used [KB]: 1663
% 1.57/0.54  % (15399)Time elapsed: 0.110 s
% 1.57/0.54  % (15399)------------------------------
% 1.57/0.54  % (15399)------------------------------
% 1.57/0.54  % (15396)Refutation not found, incomplete strategy% (15396)------------------------------
% 1.57/0.54  % (15396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.54  % (15396)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.54  
% 1.57/0.54  % (15396)Memory used [KB]: 6140
% 1.57/0.54  % (15396)Time elapsed: 0.169 s
% 1.57/0.54  % (15396)------------------------------
% 1.57/0.54  % (15396)------------------------------
% 1.57/0.55  % (15415)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.55  % (15391)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.55  % (15406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.78/0.56  % (15402)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.56  % (15398)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.78/0.56  % (15401)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.78/0.56  % (15402)Refutation not found, incomplete strategy% (15402)------------------------------
% 1.78/0.56  % (15402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.56  % (15402)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.56  
% 1.78/0.56  % (15402)Memory used [KB]: 1663
% 1.78/0.56  % (15402)Time elapsed: 0.188 s
% 1.78/0.56  % (15402)------------------------------
% 1.78/0.56  % (15402)------------------------------
% 1.78/0.56  % (15392)Refutation found. Thanks to Tanya!
% 1.78/0.56  % SZS status Theorem for theBenchmark
% 1.78/0.56  % SZS output start Proof for theBenchmark
% 1.78/0.56  fof(f1350,plain,(
% 1.78/0.56    $false),
% 1.78/0.56    inference(unit_resulting_resolution,[],[f106,f937,f126])).
% 1.78/0.56  fof(f126,plain,(
% 1.78/0.56    ( ! [X2,X3] : (~r1_tarski(k6_relat_1(k3_xboole_0(X2,X3)),k7_relat_1(k6_relat_1(X2),X3)) | k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 1.78/0.56    inference(resolution,[],[f113,f55])).
% 1.78/0.56  fof(f55,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f34])).
% 1.78/0.56  fof(f34,plain,(
% 1.78/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.56    inference(flattening,[],[f33])).
% 1.78/0.56  fof(f33,plain,(
% 1.78/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.56    inference(nnf_transformation,[],[f1])).
% 1.78/0.56  fof(f1,axiom,(
% 1.78/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.56  fof(f113,plain,(
% 1.78/0.56    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 1.78/0.56    inference(superposition,[],[f74,f76])).
% 1.78/0.56  fof(f76,plain,(
% 1.78/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f75,f37])).
% 1.78/0.56  fof(f37,plain,(
% 1.78/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.78/0.56    inference(cnf_transformation,[],[f12])).
% 1.78/0.56  fof(f12,axiom,(
% 1.78/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.78/0.56  fof(f75,plain,(
% 1.78/0.56    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.78/0.56    inference(resolution,[],[f48,f36])).
% 1.78/0.56  fof(f36,plain,(
% 1.78/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.78/0.56    inference(cnf_transformation,[],[f9])).
% 1.78/0.56  fof(f9,axiom,(
% 1.78/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.78/0.56  % (15401)Refutation not found, incomplete strategy% (15401)------------------------------
% 1.78/0.56  % (15401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.56  % (15401)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.56  
% 1.78/0.56  % (15401)Memory used [KB]: 10618
% 1.78/0.56  % (15401)Time elapsed: 0.177 s
% 1.78/0.56  % (15401)------------------------------
% 1.78/0.56  % (15401)------------------------------
% 1.78/0.56  fof(f48,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 1.78/0.56    inference(cnf_transformation,[],[f25])).
% 1.78/0.56  fof(f25,plain,(
% 1.78/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.56    inference(ennf_transformation,[],[f10])).
% 1.78/0.56  fof(f10,axiom,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 1.78/0.56  % (15385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.56  fof(f74,plain,(
% 1.78/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 1.78/0.56    inference(backward_demodulation,[],[f59,f72])).
% 1.78/0.56  fof(f72,plain,(
% 1.78/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.78/0.56    inference(resolution,[],[f47,f36])).
% 1.78/0.56  fof(f47,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f24])).
% 1.78/0.56  fof(f24,plain,(
% 1.78/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.78/0.56    inference(ennf_transformation,[],[f17])).
% 1.78/0.56  fof(f17,axiom,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.78/0.56  fof(f59,plain,(
% 1.78/0.56    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.78/0.56    inference(resolution,[],[f49,f36])).
% 1.78/0.56  fof(f49,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f26])).
% 1.78/0.56  fof(f26,plain,(
% 1.78/0.56    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.78/0.56    inference(ennf_transformation,[],[f13])).
% 1.78/0.56  fof(f13,axiom,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.78/0.56  fof(f937,plain,(
% 1.78/0.56    ( ! [X6,X5] : (r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),X6))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f925,f76])).
% 1.78/0.56  fof(f925,plain,(
% 1.78/0.56    ( ! [X6,X5] : (r1_tarski(k6_relat_1(k3_xboole_0(X5,X6)),k7_relat_1(k6_relat_1(X5),k3_xboole_0(X5,X6)))) )),
% 1.78/0.56    inference(superposition,[],[f256,f105])).
% 1.78/0.56  fof(f105,plain,(
% 1.78/0.56    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.78/0.56    inference(superposition,[],[f72,f63])).
% 1.78/0.56  fof(f63,plain,(
% 1.78/0.56    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f62,f38])).
% 1.78/0.56  fof(f38,plain,(
% 1.78/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.78/0.56    inference(cnf_transformation,[],[f12])).
% 1.78/0.56  fof(f62,plain,(
% 1.78/0.56    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.78/0.56    inference(resolution,[],[f39,f36])).
% 1.78/0.56  % (15411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.78/0.56  fof(f39,plain,(
% 1.78/0.56    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.78/0.56    inference(cnf_transformation,[],[f21])).
% 1.78/0.56  fof(f21,plain,(
% 1.78/0.56    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.78/0.56    inference(ennf_transformation,[],[f16])).
% 1.78/0.56  fof(f16,axiom,(
% 1.78/0.56    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.78/0.56  fof(f256,plain,(
% 1.78/0.56    ( ! [X6,X7,X5] : (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(X5,X6)),X7),k7_relat_1(k6_relat_1(X5),X7))) )),
% 1.78/0.56    inference(superposition,[],[f176,f109])).
% 1.78/0.56  fof(f109,plain,(
% 1.78/0.56    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1)) )),
% 1.78/0.56    inference(resolution,[],[f81,f42])).
% 1.78/0.56  fof(f42,plain,(
% 1.78/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f2])).
% 1.78/0.56  fof(f2,axiom,(
% 1.78/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.78/0.56  fof(f81,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.78/0.56    inference(forward_demodulation,[],[f80,f72])).
% 1.78/0.56  fof(f80,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f79,f37])).
% 1.78/0.56  fof(f79,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.78/0.56    inference(resolution,[],[f51,f36])).
% 1.78/0.56  fof(f51,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.78/0.56    inference(cnf_transformation,[],[f28])).
% 1.78/0.56  fof(f28,plain,(
% 1.78/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.78/0.56    inference(flattening,[],[f27])).
% 1.78/0.56  fof(f27,plain,(
% 1.78/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.78/0.56    inference(ennf_transformation,[],[f14])).
% 1.78/0.56  fof(f14,axiom,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.78/0.56  fof(f176,plain,(
% 1.78/0.56    ( ! [X14,X15,X16] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X16),X14),X15),k7_relat_1(k6_relat_1(X14),X15))) )),
% 1.78/0.56    inference(backward_demodulation,[],[f98,f173])).
% 1.78/0.56  fof(f173,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f172,f72])).
% 1.78/0.56  fof(f172,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 1.78/0.56    inference(forward_demodulation,[],[f170,f96])).
% 1.78/0.56  fof(f96,plain,(
% 1.78/0.56    ( ! [X10,X8,X9] : (k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X10) = k5_relat_1(k6_relat_1(X10),k7_relat_1(k6_relat_1(X8),X9))) )),
% 1.78/0.56    inference(resolution,[],[f78,f47])).
% 1.78/0.56  fof(f78,plain,(
% 1.78/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f77,f72])).
% 1.78/0.56  fof(f77,plain,(
% 1.78/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.78/0.56    inference(resolution,[],[f61,f36])).
% 1.78/0.56  fof(f61,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 1.78/0.56    inference(resolution,[],[f52,f36])).
% 1.78/0.56  fof(f52,plain,(
% 1.78/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f30])).
% 1.78/0.56  fof(f30,plain,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.78/0.56    inference(flattening,[],[f29])).
% 1.78/0.56  fof(f29,plain,(
% 1.78/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.78/0.56    inference(ennf_transformation,[],[f8])).
% 1.78/0.56  fof(f8,axiom,(
% 1.78/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.78/0.56  fof(f170,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.78/0.56    inference(resolution,[],[f117,f36])).
% 1.78/0.56  fof(f117,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.78/0.56    inference(forward_demodulation,[],[f115,f72])).
% 1.78/0.56  fof(f115,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.78/0.56    inference(resolution,[],[f82,f36])).
% 1.78/0.56  fof(f82,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.78/0.56    inference(resolution,[],[f41,f36])).
% 1.78/0.56  fof(f41,plain,(
% 1.78/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.78/0.56    inference(cnf_transformation,[],[f23])).
% 1.78/0.56  fof(f23,plain,(
% 1.78/0.56    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.78/0.56    inference(ennf_transformation,[],[f11])).
% 1.78/0.56  fof(f11,axiom,(
% 1.78/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.78/0.56  fof(f98,plain,(
% 1.78/0.56    ( ! [X14,X15,X16] : (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(X14),X15),k6_relat_1(X16)),k7_relat_1(k6_relat_1(X14),X15))) )),
% 1.78/0.56    inference(resolution,[],[f78,f49])).
% 1.78/0.56  fof(f106,plain,(
% 1.78/0.56    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.78/0.56    inference(superposition,[],[f35,f72])).
% 1.78/0.56  fof(f35,plain,(
% 1.78/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.78/0.56    inference(cnf_transformation,[],[f32])).
% 1.78/0.56  fof(f32,plain,(
% 1.78/0.56    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.78/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 1.78/0.56  fof(f31,plain,(
% 1.78/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.78/0.56    introduced(choice_axiom,[])).
% 1.78/0.56  fof(f20,plain,(
% 1.78/0.56    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.78/0.56    inference(ennf_transformation,[],[f19])).
% 1.78/0.56  % (15411)Refutation not found, incomplete strategy% (15411)------------------------------
% 1.78/0.56  % (15411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.56  % (15411)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.56  
% 1.78/0.56  % (15410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.78/0.56  % (15411)Memory used [KB]: 6140
% 1.78/0.56  % (15411)Time elapsed: 0.173 s
% 1.78/0.56  % (15411)------------------------------
% 1.78/0.56  % (15411)------------------------------
% 1.78/0.56  fof(f19,negated_conjecture,(
% 1.78/0.56    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.78/0.56    inference(negated_conjecture,[],[f18])).
% 1.78/0.56  fof(f18,conjecture,(
% 1.78/0.56    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.78/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.78/0.56  % SZS output end Proof for theBenchmark
% 1.78/0.56  % (15392)------------------------------
% 1.78/0.56  % (15392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.56  % (15392)Termination reason: Refutation
% 1.78/0.56  
% 1.78/0.56  % (15392)Memory used [KB]: 2814
% 1.78/0.56  % (15392)Time elapsed: 0.159 s
% 1.78/0.56  % (15392)------------------------------
% 1.78/0.56  % (15392)------------------------------
% 1.78/0.56  % (15384)Success in time 0.231 s
%------------------------------------------------------------------------------
