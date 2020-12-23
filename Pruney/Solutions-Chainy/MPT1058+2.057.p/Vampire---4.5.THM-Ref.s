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
% DateTime   : Thu Dec  3 13:07:25 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 178 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 ( 333 expanded)
%              Number of equality atoms :   60 ( 156 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f955,plain,(
    $false ),
    inference(subsumption_resolution,[],[f942,f29])).

fof(f29,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f942,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f877,f93])).

fof(f93,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK0,X1))) ),
    inference(unit_resulting_resolution,[],[f30,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f877,plain,(
    k10_relat_1(sK0,sK2) = k1_setfam_1(k2_tarski(sK1,k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f260,f154])).

fof(f154,plain,(
    sK1 = k2_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK3(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f260,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(k2_xboole_0(X1,X0),X0)) = X0 ),
    inference(forward_demodulation,[],[f254,f133])).

fof(f133,plain,(
    ! [X0,X1] : k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = X1 ),
    inference(unit_resulting_resolution,[],[f87,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(backward_demodulation,[],[f59,f86])).

fof(f86,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f85,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f85,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(forward_demodulation,[],[f84,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f46,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f84,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f81,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f44,f44,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f254,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f105,f171])).

fof(f171,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[],[f86,f73])).

fof(f73,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f72,f48])).

fof(f72,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f69,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f105,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X0)) ),
    inference(forward_demodulation,[],[f104,f86])).

fof(f104,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X2,X0))) ),
    inference(forward_demodulation,[],[f103,f86])).

fof(f103,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_tarski(X2,X0))) ),
    inference(forward_demodulation,[],[f100,f86])).

fof(f100,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2)) ),
    inference(unit_resulting_resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (16172)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.49  % (16153)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.49  % (16174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.49  % (16158)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.50  % (16169)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (16158)Refutation not found, incomplete strategy% (16158)------------------------------
% 0.22/0.50  % (16158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16173)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.50  % (16158)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16158)Memory used [KB]: 10618
% 0.22/0.50  % (16158)Time elapsed: 0.087 s
% 0.22/0.50  % (16158)------------------------------
% 0.22/0.50  % (16158)------------------------------
% 0.22/0.50  % (16174)Refutation not found, incomplete strategy% (16174)------------------------------
% 0.22/0.50  % (16174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16174)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16174)Memory used [KB]: 10746
% 0.22/0.50  % (16174)Time elapsed: 0.095 s
% 0.22/0.50  % (16174)------------------------------
% 0.22/0.50  % (16174)------------------------------
% 0.22/0.51  % (16152)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (16164)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (16147)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (16168)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (16150)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (16154)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (16170)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (16163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (16167)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (16147)Refutation not found, incomplete strategy% (16147)------------------------------
% 0.22/0.52  % (16147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16147)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16147)Memory used [KB]: 1663
% 0.22/0.52  % (16147)Time elapsed: 0.109 s
% 0.22/0.52  % (16147)------------------------------
% 0.22/0.52  % (16147)------------------------------
% 0.22/0.52  % (16151)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (16162)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (16160)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (16146)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (16161)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (16166)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (16159)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (16155)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (16156)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (16175)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (16171)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (16149)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (16175)Refutation not found, incomplete strategy% (16175)------------------------------
% 0.22/0.53  % (16175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16175)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16175)Memory used [KB]: 1663
% 0.22/0.53  % (16175)Time elapsed: 0.122 s
% 0.22/0.53  % (16175)------------------------------
% 0.22/0.53  % (16175)------------------------------
% 0.22/0.53  % (16156)Refutation not found, incomplete strategy% (16156)------------------------------
% 0.22/0.53  % (16156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (16156)Memory used [KB]: 10746
% 0.22/0.53  % (16156)Time elapsed: 0.092 s
% 0.22/0.53  % (16156)------------------------------
% 0.22/0.53  % (16156)------------------------------
% 0.22/0.54  % (16157)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (16148)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (16162)Refutation not found, incomplete strategy% (16162)------------------------------
% 0.22/0.54  % (16162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (16162)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (16162)Memory used [KB]: 10618
% 0.22/0.54  % (16162)Time elapsed: 0.131 s
% 0.22/0.54  % (16162)------------------------------
% 0.22/0.54  % (16162)------------------------------
% 0.22/0.55  % (16165)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.69/0.60  % (16165)Refutation found. Thanks to Tanya!
% 1.69/0.60  % SZS status Theorem for theBenchmark
% 1.69/0.62  % SZS output start Proof for theBenchmark
% 1.69/0.62  fof(f955,plain,(
% 1.69/0.62    $false),
% 1.69/0.62    inference(subsumption_resolution,[],[f942,f29])).
% 1.69/0.62  fof(f29,plain,(
% 1.69/0.62    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.69/0.62    inference(cnf_transformation,[],[f19])).
% 1.69/0.62  fof(f19,plain,(
% 1.69/0.62    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.69/0.62    inference(flattening,[],[f18])).
% 1.69/0.62  fof(f18,plain,(
% 1.69/0.62    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.69/0.62    inference(ennf_transformation,[],[f17])).
% 1.69/0.62  fof(f17,negated_conjecture,(
% 1.69/0.62    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.69/0.62    inference(negated_conjecture,[],[f16])).
% 1.69/0.62  fof(f16,conjecture,(
% 1.69/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.69/0.62  fof(f942,plain,(
% 1.69/0.62    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.69/0.62    inference(superposition,[],[f877,f93])).
% 1.69/0.62  fof(f93,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK0,X1)))) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f30,f50])).
% 1.69/0.62  fof(f50,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 1.69/0.62    inference(definition_unfolding,[],[f35,f47])).
% 1.69/0.62  fof(f47,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f7])).
% 1.69/0.62  fof(f7,axiom,(
% 1.69/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.69/0.62  fof(f35,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f20])).
% 1.69/0.62  fof(f20,plain,(
% 1.69/0.62    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.69/0.62    inference(ennf_transformation,[],[f14])).
% 1.69/0.62  fof(f14,axiom,(
% 1.69/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.69/0.62  fof(f30,plain,(
% 1.69/0.62    v1_relat_1(sK0)),
% 1.69/0.62    inference(cnf_transformation,[],[f19])).
% 1.69/0.62  fof(f877,plain,(
% 1.69/0.62    k10_relat_1(sK0,sK2) = k1_setfam_1(k2_tarski(sK1,k10_relat_1(sK0,sK2)))),
% 1.69/0.62    inference(superposition,[],[f260,f154])).
% 1.69/0.62  fof(f154,plain,(
% 1.69/0.62    sK1 = k2_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f28,f118])).
% 1.69/0.62  fof(f118,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X0) = X1) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f117,f52])).
% 1.69/0.62  fof(f52,plain,(
% 1.69/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.62    inference(equality_resolution,[],[f33])).
% 1.69/0.62  fof(f33,plain,(
% 1.69/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.62    inference(cnf_transformation,[],[f1])).
% 1.69/0.62  fof(f1,axiom,(
% 1.69/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.62  fof(f117,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 1.69/0.62    inference(duplicate_literal_removal,[],[f114])).
% 1.69/0.62  fof(f114,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 1.69/0.62    inference(resolution,[],[f38,f36])).
% 1.69/0.62  fof(f36,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 1.69/0.62    inference(cnf_transformation,[],[f22])).
% 1.69/0.62  fof(f22,plain,(
% 1.69/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.69/0.62    inference(flattening,[],[f21])).
% 1.69/0.62  fof(f21,plain,(
% 1.69/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.69/0.62    inference(ennf_transformation,[],[f3])).
% 1.69/0.62  fof(f3,axiom,(
% 1.69/0.62    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 1.69/0.62  fof(f38,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1) | k2_xboole_0(X0,X2) = X1) )),
% 1.69/0.62    inference(cnf_transformation,[],[f22])).
% 1.69/0.62  fof(f28,plain,(
% 1.69/0.62    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.69/0.62    inference(cnf_transformation,[],[f19])).
% 1.69/0.62  fof(f260,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k2_xboole_0(X1,X0),X0)) = X0) )),
% 1.69/0.62    inference(forward_demodulation,[],[f254,f133])).
% 1.69/0.62  fof(f133,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = X1) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f87,f39])).
% 1.69/0.62  fof(f39,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f23])).
% 1.69/0.62  fof(f23,plain,(
% 1.69/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.69/0.62    inference(ennf_transformation,[],[f2])).
% 1.69/0.62  fof(f2,axiom,(
% 1.69/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.69/0.62  fof(f87,plain,(
% 1.69/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.69/0.62    inference(backward_demodulation,[],[f59,f86])).
% 1.69/0.62  fof(f86,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f85,f48])).
% 1.69/0.62  fof(f48,plain,(
% 1.69/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.62    inference(cnf_transformation,[],[f12])).
% 1.69/0.62  fof(f12,axiom,(
% 1.69/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.69/0.62  fof(f85,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.69/0.62    inference(forward_demodulation,[],[f84,f51])).
% 1.69/0.62  fof(f51,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.69/0.62    inference(definition_unfolding,[],[f46,f47])).
% 1.69/0.62  fof(f46,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f15])).
% 1.69/0.62  fof(f15,axiom,(
% 1.69/0.62    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.69/0.62  fof(f84,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.69/0.62    inference(forward_demodulation,[],[f81,f48])).
% 1.69/0.62  fof(f81,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1)))) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f44,f44,f42])).
% 1.69/0.62  fof(f42,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f26])).
% 1.69/0.62  fof(f26,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.62    inference(ennf_transformation,[],[f11])).
% 1.69/0.62  fof(f11,axiom,(
% 1.69/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.69/0.62  fof(f44,plain,(
% 1.69/0.62    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f13])).
% 1.69/0.62  fof(f13,axiom,(
% 1.69/0.62    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.69/0.62  fof(f59,plain,(
% 1.69/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f57,f48])).
% 1.69/0.62  fof(f57,plain,(
% 1.69/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f44,f40])).
% 1.69/0.62  fof(f40,plain,(
% 1.69/0.62    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f24])).
% 1.69/0.62  fof(f24,plain,(
% 1.69/0.62    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.69/0.62    inference(ennf_transformation,[],[f8])).
% 1.69/0.62  fof(f8,axiom,(
% 1.69/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.69/0.62  fof(f254,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k2_xboole_0(X1,X0),X0)) = k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.69/0.62    inference(superposition,[],[f105,f171])).
% 1.69/0.62  fof(f171,plain,(
% 1.69/0.62    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.69/0.62    inference(superposition,[],[f86,f73])).
% 1.69/0.62  fof(f73,plain,(
% 1.69/0.62    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.69/0.62    inference(forward_demodulation,[],[f72,f48])).
% 1.69/0.62  fof(f72,plain,(
% 1.69/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f69,f49])).
% 1.69/0.62  fof(f49,plain,(
% 1.69/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.69/0.62    inference(cnf_transformation,[],[f12])).
% 1.69/0.62  fof(f69,plain,(
% 1.69/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f44,f43])).
% 1.69/0.62  fof(f43,plain,(
% 1.69/0.62    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f27])).
% 1.69/0.62  fof(f27,plain,(
% 1.69/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.62    inference(ennf_transformation,[],[f9])).
% 1.69/0.62  fof(f9,axiom,(
% 1.69/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.69/0.62  fof(f105,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(k2_xboole_0(X1,X2),X0))) )),
% 1.69/0.62    inference(forward_demodulation,[],[f104,f86])).
% 1.69/0.62  fof(f104,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k1_setfam_1(k2_tarski(X2,X0)))) )),
% 1.69/0.62    inference(forward_demodulation,[],[f103,f86])).
% 1.69/0.62  fof(f103,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_tarski(X2,X0)))) )),
% 1.69/0.62    inference(forward_demodulation,[],[f100,f86])).
% 1.69/0.62  fof(f100,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2))) )),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f44,f41])).
% 1.69/0.62  fof(f41,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f25])).
% 1.69/0.62  fof(f25,plain,(
% 1.69/0.62    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.69/0.62    inference(ennf_transformation,[],[f10])).
% 1.69/0.62  fof(f10,axiom,(
% 1.69/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.69/0.62  % SZS output end Proof for theBenchmark
% 1.69/0.62  % (16165)------------------------------
% 1.69/0.62  % (16165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (16165)Termination reason: Refutation
% 1.69/0.62  
% 1.69/0.62  % (16165)Memory used [KB]: 2686
% 1.69/0.62  % (16165)Time elapsed: 0.192 s
% 1.69/0.62  % (16165)------------------------------
% 1.69/0.62  % (16165)------------------------------
% 1.69/0.62  % (16145)Success in time 0.253 s
%------------------------------------------------------------------------------
