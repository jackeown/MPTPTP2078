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
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 146 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 381 expanded)
%              Number of equality atoms :   21 (  69 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1293,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1292,f162])).

fof(f162,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f161,f25])).

fof(f25,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f161,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f158,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f158,plain,(
    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(superposition,[],[f150,f49])).

fof(f49,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f27,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f150,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f149,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f149,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f24])).

fof(f148,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f111,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f111,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
      | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(superposition,[],[f28,f106])).

fof(f106,plain,(
    ! [X1] : k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f99,f26])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1292,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f1260,f393])).

fof(f393,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    inference(superposition,[],[f390,f106])).

fof(f390,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f263,f24])).

fof(f263,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1))) ) ),
    inference(resolution,[],[f51,f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f27,f30])).

fof(f1260,plain,(
    ! [X3] : r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X3)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f1257,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,X1))
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f58,f24])).

fof(f58,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(X2,k1_relat_1(X3))
      | ~ r1_tarski(X2,k10_relat_1(X3,X4)) ) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1257,plain,(
    ! [X23,X22] :
      ( ~ r1_tarski(X22,X23)
      | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23)) ) ),
    inference(duplicate_literal_removal,[],[f1249])).

fof(f1249,plain,(
    ! [X23,X22] :
      ( ~ r1_tarski(X22,X23)
      | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23))
      | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23)) ) ),
    inference(resolution,[],[f227,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k10_relat_1(sK0,X0),X1),k10_relat_1(sK0,X2))
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k10_relat_1(sK0,X0),X1) ) ),
    inference(resolution,[],[f224,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK0,X2))
      | r2_hidden(X0,k10_relat_1(sK0,X1))
      | ~ r1_tarski(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k10_relat_1(sK0,X1))
      | ~ r2_hidden(X0,k10_relat_1(sK0,X2))
      | ~ r2_hidden(X0,k10_relat_1(sK0,X2))
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f154,f194])).

fof(f194,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,sK0),X5)
      | ~ r2_hidden(X3,k10_relat_1(sK0,X4))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f65,f26])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k10_relat_1(X0,X2))
      | r2_hidden(sK3(X1,X2,X0),X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,X4,sK0),X5)
      | r2_hidden(X3,k10_relat_1(sK0,X5))
      | ~ r2_hidden(X3,k10_relat_1(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f152,f26])).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(sK0)
      | ~ r2_hidden(sK3(X3,X4,sK0),X5)
      | r2_hidden(X3,k10_relat_1(sK0,X5))
      | ~ r2_hidden(X3,k10_relat_1(sK0,X4)) ) ),
    inference(resolution,[],[f46,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,sK3(X2,X3,sK0)),sK0)
      | ~ r2_hidden(X2,k10_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (10059)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (10050)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10066)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (10048)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (10069)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (10051)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (10054)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (10064)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (10052)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10062)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (10070)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (10046)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10072)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (10047)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10049)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (10057)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (10060)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (10053)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10061)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10074)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10068)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (10065)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (10068)Refutation not found, incomplete strategy% (10068)------------------------------
% 0.21/0.54  % (10068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10068)Memory used [KB]: 10618
% 0.21/0.54  % (10068)Time elapsed: 0.141 s
% 0.21/0.54  % (10068)------------------------------
% 0.21/0.54  % (10068)------------------------------
% 0.21/0.54  % (10063)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (10073)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10063)Refutation not found, incomplete strategy% (10063)------------------------------
% 0.21/0.54  % (10063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10055)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (10058)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (10075)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (10071)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (10067)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (10056)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.61/0.58  % (10063)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (10063)Memory used [KB]: 10618
% 1.61/0.58  % (10063)Time elapsed: 0.143 s
% 1.61/0.58  % (10063)------------------------------
% 1.61/0.58  % (10063)------------------------------
% 2.05/0.64  % (10052)Refutation found. Thanks to Tanya!
% 2.05/0.64  % SZS status Theorem for theBenchmark
% 2.05/0.66  % SZS output start Proof for theBenchmark
% 2.05/0.66  fof(f1293,plain,(
% 2.05/0.66    $false),
% 2.05/0.66    inference(subsumption_resolution,[],[f1292,f162])).
% 2.05/0.66  fof(f162,plain,(
% 2.05/0.66    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 2.05/0.66    inference(subsumption_resolution,[],[f161,f25])).
% 2.05/0.66  fof(f25,plain,(
% 2.05/0.66    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f12,plain,(
% 2.05/0.66    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f11])).
% 2.05/0.66  fof(f11,negated_conjecture,(
% 2.05/0.66    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.05/0.66    inference(negated_conjecture,[],[f10])).
% 2.05/0.66  fof(f10,conjecture,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 2.05/0.66  fof(f161,plain,(
% 2.05/0.66    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 2.05/0.66    inference(resolution,[],[f158,f33])).
% 2.05/0.66  fof(f33,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.66  fof(f158,plain,(
% 2.05/0.66    r1_tarski(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.05/0.66    inference(superposition,[],[f150,f49])).
% 2.05/0.66  fof(f49,plain,(
% 2.05/0.66    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.05/0.66    inference(resolution,[],[f27,f24])).
% 2.05/0.66  fof(f24,plain,(
% 2.05/0.66    v1_relat_1(sK1)),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f13])).
% 2.05/0.66  fof(f13,plain,(
% 2.05/0.66    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f7])).
% 2.05/0.66  fof(f7,axiom,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.05/0.66  fof(f150,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f149,f26])).
% 2.05/0.66  fof(f26,plain,(
% 2.05/0.66    v1_relat_1(sK0)),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f149,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK0)) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f148,f24])).
% 2.05/0.66  fof(f148,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X0)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 2.05/0.66    inference(resolution,[],[f111,f30])).
% 2.05/0.66  fof(f30,plain,(
% 2.05/0.66    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f17])).
% 2.05/0.66  fof(f17,plain,(
% 2.05/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.05/0.66    inference(flattening,[],[f16])).
% 2.05/0.66  fof(f16,plain,(
% 2.05/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f4])).
% 2.05/0.66  fof(f4,axiom,(
% 2.05/0.66    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.05/0.66  fof(f111,plain,(
% 2.05/0.66    ( ! [X1] : (~v1_relat_1(k5_relat_1(sK0,sK1)) | r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X1)),k1_relat_1(k5_relat_1(sK0,sK1)))) )),
% 2.05/0.66    inference(superposition,[],[f28,f106])).
% 2.05/0.66  fof(f106,plain,(
% 2.05/0.66    ( ! [X1] : (k10_relat_1(k5_relat_1(sK0,sK1),X1) = k10_relat_1(sK0,k10_relat_1(sK1,X1))) )),
% 2.05/0.66    inference(resolution,[],[f99,f26])).
% 2.05/0.66  fof(f99,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))) )),
% 2.05/0.66    inference(resolution,[],[f29,f24])).
% 2.05/0.66  fof(f29,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f15])).
% 2.05/0.66  fof(f15,plain,(
% 2.05/0.66    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f8])).
% 2.05/0.66  fof(f8,axiom,(
% 2.05/0.66    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 2.05/0.66  fof(f28,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f14])).
% 2.05/0.66  fof(f14,plain,(
% 2.05/0.66    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f6])).
% 2.05/0.66  fof(f6,axiom,(
% 2.05/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.05/0.66  fof(f1292,plain,(
% 2.05/0.66    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 2.05/0.66    inference(superposition,[],[f1260,f393])).
% 2.05/0.66  fof(f393,plain,(
% 2.05/0.66    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 2.05/0.66    inference(superposition,[],[f390,f106])).
% 2.05/0.66  fof(f390,plain,(
% 2.05/0.66    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))),
% 2.05/0.66    inference(resolution,[],[f263,f24])).
% 2.05/0.66  fof(f263,plain,(
% 2.05/0.66    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(sK0,X1)) = k10_relat_1(k5_relat_1(sK0,X1),k2_relat_1(k5_relat_1(sK0,X1)))) )),
% 2.05/0.66    inference(resolution,[],[f51,f26])).
% 2.05/0.66  fof(f51,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(k5_relat_1(X0,X1),k2_relat_1(k5_relat_1(X0,X1)))) )),
% 2.05/0.66    inference(resolution,[],[f27,f30])).
% 2.05/0.66  fof(f1260,plain,(
% 2.05/0.66    ( ! [X3] : (r1_tarski(k10_relat_1(sK0,k10_relat_1(sK1,X3)),k10_relat_1(sK0,k1_relat_1(sK1)))) )),
% 2.05/0.66    inference(resolution,[],[f1257,f66])).
% 2.05/0.66  fof(f66,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.05/0.66    inference(resolution,[],[f62,f44])).
% 2.05/0.66  fof(f44,plain,(
% 2.05/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.66    inference(equality_resolution,[],[f32])).
% 2.05/0.66  fof(f32,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f2])).
% 2.05/0.66  fof(f62,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(sK1,X1)) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 2.05/0.66    inference(resolution,[],[f58,f24])).
% 2.05/0.66  fof(f58,plain,(
% 2.05/0.66    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | r1_tarski(X2,k1_relat_1(X3)) | ~r1_tarski(X2,k10_relat_1(X3,X4))) )),
% 2.05/0.66    inference(resolution,[],[f43,f28])).
% 2.05/0.66  fof(f43,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f23])).
% 2.05/0.66  fof(f23,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.05/0.66    inference(flattening,[],[f22])).
% 2.05/0.66  fof(f22,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.05/0.66    inference(ennf_transformation,[],[f3])).
% 2.05/0.66  fof(f3,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.05/0.66  fof(f1257,plain,(
% 2.05/0.66    ( ! [X23,X22] : (~r1_tarski(X22,X23) | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23))) )),
% 2.05/0.66    inference(duplicate_literal_removal,[],[f1249])).
% 2.05/0.66  fof(f1249,plain,(
% 2.05/0.66    ( ! [X23,X22] : (~r1_tarski(X22,X23) | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23)) | r1_tarski(k10_relat_1(sK0,X22),k10_relat_1(sK0,X23))) )),
% 2.05/0.66    inference(resolution,[],[f227,f36])).
% 2.05/0.66  fof(f36,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f18])).
% 2.05/0.66  fof(f18,plain,(
% 2.05/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.05/0.66    inference(ennf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.05/0.66  fof(f227,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK2(k10_relat_1(sK0,X0),X1),k10_relat_1(sK0,X2)) | ~r1_tarski(X0,X2) | r1_tarski(k10_relat_1(sK0,X0),X1)) )),
% 2.05/0.66    inference(resolution,[],[f224,f35])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f18])).
% 2.05/0.66  fof(f224,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(sK0,X2)) | r2_hidden(X0,k10_relat_1(sK0,X1)) | ~r1_tarski(X2,X1)) )),
% 2.05/0.66    inference(duplicate_literal_removal,[],[f219])).
% 2.05/0.66  fof(f219,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (r2_hidden(X0,k10_relat_1(sK0,X1)) | ~r2_hidden(X0,k10_relat_1(sK0,X2)) | ~r2_hidden(X0,k10_relat_1(sK0,X2)) | ~r1_tarski(X2,X1)) )),
% 2.05/0.66    inference(resolution,[],[f154,f194])).
% 2.05/0.66  fof(f194,plain,(
% 2.05/0.66    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,sK0),X5) | ~r2_hidden(X3,k10_relat_1(sK0,X4)) | ~r1_tarski(X4,X5)) )),
% 2.05/0.66    inference(resolution,[],[f65,f26])).
% 2.05/0.66  fof(f65,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X1,k10_relat_1(X0,X2)) | r2_hidden(sK3(X1,X2,X0),X3) | ~r1_tarski(X2,X3)) )),
% 2.05/0.66    inference(resolution,[],[f41,f34])).
% 2.05/0.66  fof(f34,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f18])).
% 2.05/0.66  fof(f41,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f21])).
% 2.05/0.66  fof(f21,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.05/0.66    inference(ennf_transformation,[],[f5])).
% 2.05/0.66  fof(f5,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 2.05/0.66  fof(f154,plain,(
% 2.05/0.66    ( ! [X4,X5,X3] : (~r2_hidden(sK3(X3,X4,sK0),X5) | r2_hidden(X3,k10_relat_1(sK0,X5)) | ~r2_hidden(X3,k10_relat_1(sK0,X4))) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f152,f26])).
% 2.05/0.66  fof(f152,plain,(
% 2.05/0.66    ( ! [X4,X5,X3] : (~v1_relat_1(sK0) | ~r2_hidden(sK3(X3,X4,sK0),X5) | r2_hidden(X3,k10_relat_1(sK0,X5)) | ~r2_hidden(X3,k10_relat_1(sK0,X4))) )),
% 2.05/0.66    inference(resolution,[],[f46,f103])).
% 2.05/0.66  fof(f103,plain,(
% 2.05/0.66    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,sK3(X2,X3,sK0)),sK0) | ~r2_hidden(X2,k10_relat_1(sK0,X3))) )),
% 2.05/0.66    inference(resolution,[],[f40,f26])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f21])).
% 2.05/0.66  fof(f46,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.05/0.66    inference(subsumption_resolution,[],[f42,f38])).
% 2.05/0.66  fof(f38,plain,(
% 2.05/0.66    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f20])).
% 2.05/0.66  fof(f20,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.05/0.66    inference(flattening,[],[f19])).
% 2.05/0.66  fof(f19,plain,(
% 2.05/0.66    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.05/0.66    inference(ennf_transformation,[],[f9])).
% 2.05/0.66  fof(f9,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.05/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 2.05/0.66  fof(f42,plain,(
% 2.05/0.66    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.05/0.66    inference(cnf_transformation,[],[f21])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (10052)------------------------------
% 2.05/0.66  % (10052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (10052)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (10052)Memory used [KB]: 7291
% 2.05/0.66  % (10052)Time elapsed: 0.235 s
% 2.05/0.66  % (10052)------------------------------
% 2.05/0.66  % (10052)------------------------------
% 2.05/0.66  % (10045)Success in time 0.298 s
%------------------------------------------------------------------------------
