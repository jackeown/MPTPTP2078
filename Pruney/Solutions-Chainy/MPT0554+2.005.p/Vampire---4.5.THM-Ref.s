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
% DateTime   : Thu Dec  3 12:49:51 EST 2020

% Result     : Theorem 10.64s
% Output     : Refutation 10.64s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 196 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   25
%              Number of atoms          :  147 ( 399 expanded)
%              Number of equality atoms :   26 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15565,f21])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f15565,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f1186,f15432])).

fof(f15432,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f15429,f59])).

fof(f59,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(resolution,[],[f28,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f15429,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f15179,f99])).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f95,f24])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(X0,k1_xboole_0))
      | k2_xboole_0(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f86,f28])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f77,f25])).

fof(f77,plain,(
    ! [X3] : r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f33,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f15179,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f15161,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f15161,plain,(
    ! [X6] : r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),X6) ),
    inference(resolution,[],[f15065,f41])).

fof(f15065,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X2,sK1),X3) ) ),
    inference(forward_demodulation,[],[f15059,f25])).

fof(f15059,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,sK1),X3)
      | ~ r1_tarski(X2,k2_xboole_0(sK1,sK0)) ) ),
    inference(resolution,[],[f13763,f33])).

fof(f13763,plain,(
    ! [X54,X53] :
      ( ~ r1_tarski(k4_xboole_0(X53,sK1),sK0)
      | r1_tarski(k4_xboole_0(X53,sK1),X54) ) ),
    inference(superposition,[],[f1646,f13722])).

fof(f13722,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    inference(subsumption_resolution,[],[f13709,f46])).

fof(f13709,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k2_xboole_0(k4_xboole_0(X0,sK1),sK0))
      | sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) ) ),
    inference(resolution,[],[f13704,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(resolution,[],[f33,f28])).

fof(f13704,plain,(
    ! [X11] : r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1))) ),
    inference(duplicate_literal_removal,[],[f13600])).

fof(f13600,plain,(
    ! [X11] :
      ( r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1)))
      | r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1))) ) ),
    inference(resolution,[],[f4056,f4103])).

fof(f4103,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(sK0,X4),k4_xboole_0(X5,sK1))
      | r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f4085,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f4085,plain,(
    ! [X104] :
      ( r2_hidden(sK3(sK0,X104),sK1)
      | r1_tarski(sK0,X104) ) ),
    inference(subsumption_resolution,[],[f4041,f1335])).

fof(f1335,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,X3),k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f52,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(backward_demodulation,[],[f64,f99])).

fof(f64,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k2_xboole_0(X4,k1_xboole_0))
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f33,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),k4_xboole_0(X2,X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f4041,plain,(
    ! [X104] :
      ( r2_hidden(sK3(sK0,X104),k1_xboole_0)
      | r2_hidden(sK3(sK0,X104),sK1)
      | r1_tarski(sK0,X104) ) ),
    inference(superposition,[],[f180,f125])).

fof(f125,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f102,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,X2))
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f4056,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,k4_xboole_0(X5,X6)),X6)
      | r1_tarski(X5,k4_xboole_0(X5,X6)) ) ),
    inference(duplicate_literal_removal,[],[f4006])).

fof(f4006,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5,k4_xboole_0(X5,X6)),X6)
      | r1_tarski(X5,k4_xboole_0(X5,X6))
      | r1_tarski(X5,k4_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f180,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1646,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k4_xboole_0(X15,X14))
      | r1_tarski(X14,X16) ) ),
    inference(duplicate_literal_removal,[],[f1640])).

fof(f1640,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k4_xboole_0(X15,X14))
      | r1_tarski(X14,X16)
      | r1_tarski(X14,X16) ) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f29,f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1186,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f24,f346])).

fof(f346,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (26242)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (26258)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (26258)Refutation not found, incomplete strategy% (26258)------------------------------
% 0.21/0.54  % (26258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26258)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26258)Memory used [KB]: 10618
% 0.21/0.54  % (26258)Time elapsed: 0.106 s
% 0.21/0.54  % (26258)------------------------------
% 0.21/0.54  % (26258)------------------------------
% 0.21/0.56  % (26247)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (26246)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (26251)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (26251)Refutation not found, incomplete strategy% (26251)------------------------------
% 0.21/0.58  % (26251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (26251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (26251)Memory used [KB]: 10618
% 0.21/0.58  % (26251)Time elapsed: 0.151 s
% 0.21/0.58  % (26251)------------------------------
% 0.21/0.58  % (26251)------------------------------
% 0.21/0.58  % (26250)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (26256)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.59  % (26243)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (26264)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (26270)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (26241)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.59  % (26244)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (26245)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (26262)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.60  % (26248)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.60  % (26263)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  % (26255)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (26260)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (26254)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.60  % (26249)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.61  % (26253)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.61  % (26252)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.61  % (26267)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.61  % (26268)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.61  % (26263)Refutation not found, incomplete strategy% (26263)------------------------------
% 0.21/0.61  % (26263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (26265)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.61  % (26257)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (26261)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.61  % (26269)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.93/0.62  % (26259)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.93/0.62  % (26263)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.62  
% 1.93/0.62  % (26263)Memory used [KB]: 10746
% 1.93/0.62  % (26263)Time elapsed: 0.184 s
% 1.93/0.62  % (26263)------------------------------
% 1.93/0.62  % (26263)------------------------------
% 1.93/0.62  % (26252)Refutation not found, incomplete strategy% (26252)------------------------------
% 1.93/0.62  % (26252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (26266)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.93/0.63  % (26252)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.63  
% 1.93/0.63  % (26252)Memory used [KB]: 10618
% 1.93/0.63  % (26252)Time elapsed: 0.203 s
% 1.93/0.63  % (26252)------------------------------
% 1.93/0.63  % (26252)------------------------------
% 2.24/0.69  % (26308)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.01/0.77  % (26309)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.01/0.80  % (26311)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.01/0.81  % (26310)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.01/0.82  % (26246)Time limit reached!
% 3.01/0.82  % (26246)------------------------------
% 3.01/0.82  % (26246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.82  % (26246)Termination reason: Time limit
% 3.01/0.82  
% 3.01/0.82  % (26246)Memory used [KB]: 8059
% 3.01/0.82  % (26246)Time elapsed: 0.404 s
% 3.01/0.82  % (26246)------------------------------
% 3.01/0.82  % (26246)------------------------------
% 3.99/0.93  % (26352)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.99/0.93  % (26253)Time limit reached!
% 3.99/0.93  % (26253)------------------------------
% 3.99/0.93  % (26253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.95  % (26241)Time limit reached!
% 4.33/0.95  % (26241)------------------------------
% 4.33/0.95  % (26241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.95  % (26253)Termination reason: Time limit
% 4.33/0.95  
% 4.33/0.95  % (26253)Memory used [KB]: 8955
% 4.33/0.95  % (26253)Time elapsed: 0.513 s
% 4.33/0.95  % (26253)------------------------------
% 4.33/0.95  % (26253)------------------------------
% 4.41/0.95  % (26242)Time limit reached!
% 4.41/0.95  % (26242)------------------------------
% 4.41/0.95  % (26242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.95  % (26242)Termination reason: Time limit
% 4.41/0.95  
% 4.41/0.95  % (26242)Memory used [KB]: 10746
% 4.41/0.95  % (26242)Time elapsed: 0.520 s
% 4.41/0.95  % (26242)------------------------------
% 4.41/0.95  % (26242)------------------------------
% 4.41/0.97  % (26241)Termination reason: Time limit
% 4.41/0.97  % (26241)Termination phase: Saturation
% 4.41/0.97  
% 4.41/0.97  % (26241)Memory used [KB]: 4605
% 4.41/0.97  % (26241)Time elapsed: 0.500 s
% 4.41/0.97  % (26241)------------------------------
% 4.41/0.97  % (26241)------------------------------
% 4.85/1.03  % (26269)Time limit reached!
% 4.85/1.03  % (26269)------------------------------
% 4.85/1.03  % (26269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.04  % (26257)Time limit reached!
% 4.85/1.04  % (26257)------------------------------
% 4.85/1.04  % (26257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.04  % (26269)Termination reason: Time limit
% 4.85/1.04  
% 4.85/1.04  % (26269)Memory used [KB]: 8443
% 4.85/1.04  % (26269)Time elapsed: 0.611 s
% 4.85/1.04  % (26269)------------------------------
% 4.85/1.04  % (26269)------------------------------
% 4.85/1.04  % (26257)Termination reason: Time limit
% 4.85/1.04  % (26257)Termination phase: Saturation
% 4.85/1.04  
% 4.85/1.04  % (26257)Memory used [KB]: 15863
% 4.85/1.04  % (26257)Time elapsed: 0.600 s
% 4.85/1.04  % (26257)------------------------------
% 4.85/1.04  % (26257)------------------------------
% 5.20/1.07  % (26413)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.20/1.07  % (26419)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.20/1.09  % (26248)Time limit reached!
% 5.20/1.09  % (26248)------------------------------
% 5.20/1.09  % (26248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.20/1.09  % (26311)Time limit reached!
% 5.20/1.09  % (26311)------------------------------
% 5.20/1.09  % (26311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.20/1.09  % (26433)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.20/1.10  % (26311)Termination reason: Time limit
% 5.20/1.10  
% 5.20/1.10  % (26311)Memory used [KB]: 7803
% 5.20/1.10  % (26311)Time elapsed: 0.420 s
% 5.20/1.10  % (26311)------------------------------
% 5.20/1.10  % (26311)------------------------------
% 5.20/1.10  % (26248)Termination reason: Time limit
% 5.20/1.10  
% 5.20/1.10  % (26248)Memory used [KB]: 10362
% 5.20/1.10  % (26248)Time elapsed: 0.624 s
% 5.20/1.10  % (26248)------------------------------
% 5.20/1.10  % (26248)------------------------------
% 6.25/1.17  % (26461)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.25/1.17  % (26462)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.58/1.22  % (26473)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.58/1.23  % (26474)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.01/1.25  % (26262)Time limit reached!
% 7.01/1.25  % (26262)------------------------------
% 7.01/1.25  % (26262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.25  % (26262)Termination reason: Time limit
% 7.01/1.25  % (26262)Termination phase: Saturation
% 7.01/1.25  
% 7.01/1.25  % (26262)Memory used [KB]: 6268
% 7.01/1.25  % (26262)Time elapsed: 0.800 s
% 7.01/1.25  % (26262)------------------------------
% 7.01/1.25  % (26262)------------------------------
% 7.01/1.26  % (26352)Time limit reached!
% 7.01/1.26  % (26352)------------------------------
% 7.01/1.26  % (26352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.26  % (26352)Termination reason: Time limit
% 7.01/1.26  % (26352)Termination phase: Saturation
% 7.01/1.26  
% 7.01/1.26  % (26352)Memory used [KB]: 14200
% 7.01/1.26  % (26352)Time elapsed: 0.400 s
% 7.01/1.26  % (26352)------------------------------
% 7.01/1.26  % (26352)------------------------------
% 7.74/1.39  % (26518)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.13/1.40  % (26529)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.13/1.44  % (26243)Time limit reached!
% 8.13/1.44  % (26243)------------------------------
% 8.13/1.44  % (26243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.48/1.45  % (26243)Termination reason: Time limit
% 8.48/1.45  
% 8.48/1.45  % (26243)Memory used [KB]: 17398
% 8.48/1.45  % (26243)Time elapsed: 1.021 s
% 8.48/1.45  % (26243)------------------------------
% 8.48/1.45  % (26243)------------------------------
% 9.20/1.59  % (26550)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.58/1.64  % (26267)Time limit reached!
% 9.58/1.64  % (26267)------------------------------
% 9.58/1.64  % (26267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.98/1.65  % (26267)Termination reason: Time limit
% 9.98/1.65  
% 9.98/1.65  % (26267)Memory used [KB]: 19573
% 9.98/1.65  % (26267)Time elapsed: 1.217 s
% 9.98/1.65  % (26267)------------------------------
% 9.98/1.65  % (26267)------------------------------
% 10.64/1.76  % (26256)Time limit reached!
% 10.64/1.76  % (26256)------------------------------
% 10.64/1.76  % (26256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.64/1.76  % (26256)Termination reason: Time limit
% 10.64/1.76  % (26256)Termination phase: Saturation
% 10.64/1.76  
% 10.64/1.76  % (26256)Memory used [KB]: 12281
% 10.64/1.76  % (26256)Time elapsed: 1.300 s
% 10.64/1.76  % (26256)------------------------------
% 10.64/1.76  % (26256)------------------------------
% 10.64/1.77  % (26247)Refutation found. Thanks to Tanya!
% 10.64/1.77  % SZS status Theorem for theBenchmark
% 10.64/1.78  % SZS output start Proof for theBenchmark
% 10.64/1.78  fof(f15655,plain,(
% 10.64/1.78    $false),
% 10.64/1.78    inference(subsumption_resolution,[],[f15565,f21])).
% 10.64/1.78  fof(f21,plain,(
% 10.64/1.78    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 10.64/1.78    inference(cnf_transformation,[],[f14])).
% 10.64/1.78  fof(f14,plain,(
% 10.64/1.78    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 10.64/1.78    inference(flattening,[],[f13])).
% 10.64/1.78  fof(f13,plain,(
% 10.64/1.78    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 10.64/1.78    inference(ennf_transformation,[],[f12])).
% 10.64/1.78  fof(f12,negated_conjecture,(
% 10.64/1.78    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 10.64/1.78    inference(negated_conjecture,[],[f11])).
% 10.64/1.78  fof(f11,conjecture,(
% 10.64/1.78    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 10.64/1.78  fof(f15565,plain,(
% 10.64/1.78    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 10.64/1.78    inference(superposition,[],[f1186,f15432])).
% 10.64/1.78  fof(f15432,plain,(
% 10.64/1.78    sK1 = k2_xboole_0(sK0,sK1)),
% 10.64/1.78    inference(resolution,[],[f15429,f59])).
% 10.64/1.78  fof(f59,plain,(
% 10.64/1.78    ( ! [X4,X5] : (~r1_tarski(k2_xboole_0(X4,X5),X5) | k2_xboole_0(X4,X5) = X5) )),
% 10.64/1.78    inference(resolution,[],[f28,f46])).
% 10.64/1.78  fof(f46,plain,(
% 10.64/1.78    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 10.64/1.78    inference(superposition,[],[f24,f25])).
% 10.64/1.78  fof(f25,plain,(
% 10.64/1.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 10.64/1.78    inference(cnf_transformation,[],[f1])).
% 10.64/1.78  fof(f1,axiom,(
% 10.64/1.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 10.64/1.78  fof(f24,plain,(
% 10.64/1.78    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 10.64/1.78    inference(cnf_transformation,[],[f9])).
% 10.64/1.78  fof(f9,axiom,(
% 10.64/1.78    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 10.64/1.78  fof(f28,plain,(
% 10.64/1.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 10.64/1.78    inference(cnf_transformation,[],[f4])).
% 10.64/1.78  fof(f4,axiom,(
% 10.64/1.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.64/1.78  fof(f15429,plain,(
% 10.64/1.78    r1_tarski(k2_xboole_0(sK0,sK1),sK1)),
% 10.64/1.78    inference(superposition,[],[f15179,f99])).
% 10.64/1.78  fof(f99,plain,(
% 10.64/1.78    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.64/1.78    inference(subsumption_resolution,[],[f95,f24])).
% 10.64/1.78  fof(f95,plain,(
% 10.64/1.78    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(X0,k1_xboole_0)) | k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.64/1.78    inference(resolution,[],[f86,f28])).
% 10.64/1.78  fof(f86,plain,(
% 10.64/1.78    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k1_xboole_0),X0)) )),
% 10.64/1.78    inference(superposition,[],[f77,f25])).
% 10.64/1.78  fof(f77,plain,(
% 10.64/1.78    ( ! [X3] : (r1_tarski(k2_xboole_0(k1_xboole_0,X3),X3)) )),
% 10.64/1.78    inference(resolution,[],[f65,f41])).
% 10.64/1.78  fof(f41,plain,(
% 10.64/1.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.64/1.78    inference(equality_resolution,[],[f27])).
% 10.64/1.78  fof(f27,plain,(
% 10.64/1.78    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.64/1.78    inference(cnf_transformation,[],[f4])).
% 10.64/1.78  fof(f65,plain,(
% 10.64/1.78    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(superposition,[],[f33,f23])).
% 10.64/1.78  fof(f23,plain,(
% 10.64/1.78    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 10.64/1.78    inference(cnf_transformation,[],[f6])).
% 10.64/1.78  fof(f6,axiom,(
% 10.64/1.78    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 10.64/1.78  fof(f33,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 10.64/1.78    inference(cnf_transformation,[],[f17])).
% 10.64/1.78  fof(f17,plain,(
% 10.64/1.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 10.64/1.78    inference(ennf_transformation,[],[f7])).
% 10.64/1.78  fof(f7,axiom,(
% 10.64/1.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 10.64/1.78  fof(f15179,plain,(
% 10.64/1.78    ( ! [X0] : (r1_tarski(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0))) )),
% 10.64/1.78    inference(resolution,[],[f15161,f34])).
% 10.64/1.78  fof(f34,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 10.64/1.78    inference(cnf_transformation,[],[f18])).
% 10.64/1.78  fof(f18,plain,(
% 10.64/1.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 10.64/1.78    inference(ennf_transformation,[],[f8])).
% 10.64/1.78  fof(f8,axiom,(
% 10.64/1.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 10.64/1.78  fof(f15161,plain,(
% 10.64/1.78    ( ! [X6] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),sK1),X6)) )),
% 10.64/1.78    inference(resolution,[],[f15065,f41])).
% 10.64/1.78  fof(f15065,plain,(
% 10.64/1.78    ( ! [X2,X3] : (~r1_tarski(X2,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X2,sK1),X3)) )),
% 10.64/1.78    inference(forward_demodulation,[],[f15059,f25])).
% 10.64/1.78  fof(f15059,plain,(
% 10.64/1.78    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,sK1),X3) | ~r1_tarski(X2,k2_xboole_0(sK1,sK0))) )),
% 10.64/1.78    inference(resolution,[],[f13763,f33])).
% 10.64/1.78  fof(f13763,plain,(
% 10.64/1.78    ( ! [X54,X53] : (~r1_tarski(k4_xboole_0(X53,sK1),sK0) | r1_tarski(k4_xboole_0(X53,sK1),X54)) )),
% 10.64/1.78    inference(superposition,[],[f1646,f13722])).
% 10.64/1.78  fof(f13722,plain,(
% 10.64/1.78    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 10.64/1.78    inference(subsumption_resolution,[],[f13709,f46])).
% 10.64/1.78  fof(f13709,plain,(
% 10.64/1.78    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(k4_xboole_0(X0,sK1),sK0)) | sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 10.64/1.78    inference(resolution,[],[f13704,f63])).
% 10.64/1.78  fof(f63,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (~r1_tarski(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | k4_xboole_0(X0,X1) = X2) )),
% 10.64/1.78    inference(resolution,[],[f33,f28])).
% 10.64/1.78  fof(f13704,plain,(
% 10.64/1.78    ( ! [X11] : (r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1)))) )),
% 10.64/1.78    inference(duplicate_literal_removal,[],[f13600])).
% 10.64/1.78  fof(f13600,plain,(
% 10.64/1.78    ( ! [X11] : (r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1))) | r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(X11,sK1)))) )),
% 10.64/1.78    inference(resolution,[],[f4056,f4103])).
% 10.64/1.78  fof(f4103,plain,(
% 10.64/1.78    ( ! [X4,X5] : (~r2_hidden(sK3(sK0,X4),k4_xboole_0(X5,sK1)) | r1_tarski(sK0,X4)) )),
% 10.64/1.78    inference(resolution,[],[f4085,f44])).
% 10.64/1.78  fof(f44,plain,(
% 10.64/1.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 10.64/1.78    inference(equality_resolution,[],[f39])).
% 10.64/1.78  fof(f39,plain,(
% 10.64/1.78    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 10.64/1.78    inference(cnf_transformation,[],[f3])).
% 10.64/1.78  fof(f3,axiom,(
% 10.64/1.78    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 10.64/1.78  fof(f4085,plain,(
% 10.64/1.78    ( ! [X104] : (r2_hidden(sK3(sK0,X104),sK1) | r1_tarski(sK0,X104)) )),
% 10.64/1.78    inference(subsumption_resolution,[],[f4041,f1335])).
% 10.64/1.78  fof(f1335,plain,(
% 10.64/1.78    ( ! [X2,X3] : (~r2_hidden(sK3(X2,X3),k1_xboole_0) | r1_tarski(X2,X3)) )),
% 10.64/1.78    inference(superposition,[],[f52,f119])).
% 10.64/1.78  fof(f119,plain,(
% 10.64/1.78    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 10.64/1.78    inference(resolution,[],[f102,f41])).
% 10.64/1.78  fof(f102,plain,(
% 10.64/1.78    ( ! [X4,X3] : (~r1_tarski(X3,X4) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 10.64/1.78    inference(backward_demodulation,[],[f64,f99])).
% 10.64/1.78  fof(f64,plain,(
% 10.64/1.78    ( ! [X4,X3] : (~r1_tarski(X3,k2_xboole_0(X4,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 10.64/1.78    inference(resolution,[],[f33,f56])).
% 10.64/1.78  fof(f56,plain,(
% 10.64/1.78    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 10.64/1.78    inference(resolution,[],[f28,f22])).
% 10.64/1.78  fof(f22,plain,(
% 10.64/1.78    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 10.64/1.78    inference(cnf_transformation,[],[f5])).
% 10.64/1.78  fof(f5,axiom,(
% 10.64/1.78    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 10.64/1.78  fof(f52,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),k4_xboole_0(X2,X0)) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(resolution,[],[f44,f30])).
% 10.64/1.78  fof(f30,plain,(
% 10.64/1.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(cnf_transformation,[],[f15])).
% 10.64/1.78  fof(f15,plain,(
% 10.64/1.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 10.64/1.78    inference(ennf_transformation,[],[f2])).
% 10.64/1.78  fof(f2,axiom,(
% 10.64/1.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 10.64/1.78  fof(f4041,plain,(
% 10.64/1.78    ( ! [X104] : (r2_hidden(sK3(sK0,X104),k1_xboole_0) | r2_hidden(sK3(sK0,X104),sK1) | r1_tarski(sK0,X104)) )),
% 10.64/1.78    inference(superposition,[],[f180,f125])).
% 10.64/1.78  fof(f125,plain,(
% 10.64/1.78    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 10.64/1.78    inference(resolution,[],[f102,f20])).
% 10.64/1.78  fof(f20,plain,(
% 10.64/1.78    r1_tarski(sK0,sK1)),
% 10.64/1.78    inference(cnf_transformation,[],[f14])).
% 10.64/1.78  fof(f180,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,X2)) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(resolution,[],[f43,f30])).
% 10.64/1.78  fof(f43,plain,(
% 10.64/1.78    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 10.64/1.78    inference(equality_resolution,[],[f40])).
% 10.64/1.78  fof(f40,plain,(
% 10.64/1.78    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 10.64/1.78    inference(cnf_transformation,[],[f3])).
% 10.64/1.78  fof(f4056,plain,(
% 10.64/1.78    ( ! [X6,X5] : (r2_hidden(sK3(X5,k4_xboole_0(X5,X6)),X6) | r1_tarski(X5,k4_xboole_0(X5,X6))) )),
% 10.64/1.78    inference(duplicate_literal_removal,[],[f4006])).
% 10.64/1.78  fof(f4006,plain,(
% 10.64/1.78    ( ! [X6,X5] : (r2_hidden(sK3(X5,k4_xboole_0(X5,X6)),X6) | r1_tarski(X5,k4_xboole_0(X5,X6)) | r1_tarski(X5,k4_xboole_0(X5,X6))) )),
% 10.64/1.78    inference(resolution,[],[f180,f31])).
% 10.64/1.78  fof(f31,plain,(
% 10.64/1.78    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(cnf_transformation,[],[f15])).
% 10.64/1.78  fof(f1646,plain,(
% 10.64/1.78    ( ! [X14,X15,X16] : (~r1_tarski(X14,k4_xboole_0(X15,X14)) | r1_tarski(X14,X16)) )),
% 10.64/1.78    inference(duplicate_literal_removal,[],[f1640])).
% 10.64/1.78  fof(f1640,plain,(
% 10.64/1.78    ( ! [X14,X15,X16] : (~r1_tarski(X14,k4_xboole_0(X15,X14)) | r1_tarski(X14,X16) | r1_tarski(X14,X16)) )),
% 10.64/1.78    inference(resolution,[],[f62,f52])).
% 10.64/1.78  fof(f62,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(resolution,[],[f29,f30])).
% 10.64/1.78  fof(f29,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 10.64/1.78    inference(cnf_transformation,[],[f15])).
% 10.64/1.78  fof(f1186,plain,(
% 10.64/1.78    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,k2_xboole_0(X0,X1)))) )),
% 10.64/1.78    inference(superposition,[],[f24,f346])).
% 10.64/1.78  fof(f346,plain,(
% 10.64/1.78    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 10.64/1.78    inference(resolution,[],[f32,f19])).
% 10.64/1.78  fof(f19,plain,(
% 10.64/1.78    v1_relat_1(sK2)),
% 10.64/1.78    inference(cnf_transformation,[],[f14])).
% 10.64/1.78  fof(f32,plain,(
% 10.64/1.78    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 10.64/1.78    inference(cnf_transformation,[],[f16])).
% 10.64/1.78  fof(f16,plain,(
% 10.64/1.78    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 10.64/1.78    inference(ennf_transformation,[],[f10])).
% 10.64/1.78  fof(f10,axiom,(
% 10.64/1.78    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 10.64/1.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 10.64/1.78  % SZS output end Proof for theBenchmark
% 10.64/1.78  % (26247)------------------------------
% 10.64/1.78  % (26247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.64/1.78  % (26247)Termination reason: Refutation
% 10.64/1.78  
% 10.64/1.78  % (26247)Memory used [KB]: 19573
% 10.64/1.78  % (26247)Time elapsed: 1.349 s
% 10.64/1.78  % (26247)------------------------------
% 10.64/1.78  % (26247)------------------------------
% 10.64/1.78  % (26551)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 10.64/1.79  % (26240)Success in time 1.428 s
%------------------------------------------------------------------------------
