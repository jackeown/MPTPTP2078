%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:09 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   22
%              Number of atoms          :  170 ( 376 expanded)
%              Number of equality atoms :   12 (  37 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f930,plain,(
    $false ),
    inference(subsumption_resolution,[],[f929,f46])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f929,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f928,f44])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f928,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f926,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f926,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f912,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f912,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f911,f117])).

fof(f117,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_relat_1(sK1))
      | ~ r1_tarski(X2,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f85,f98])).

fof(f98,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f43,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f57])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f911,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f910,f45])).

fof(f45,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f910,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f907,f44])).

fof(f907,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f896,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f88,f100])).

fof(f100,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f46,f83])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f57])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f896,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(X7),k3_relat_1(sK1))
      | ~ r1_tarski(X7,sK1) ) ),
    inference(subsumption_resolution,[],[f895,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f97,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f895,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(X7),k3_relat_1(sK1))
      | ~ r1_tarski(X7,sK1)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f892,f43])).

fof(f892,plain,(
    ! [X7] :
      ( r1_tarski(k1_relat_1(X7),k3_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(X7,sK1)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f875,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f875,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f873,f85])).

fof(f873,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK1))))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f871,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f871,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_relat_1(sK1))
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(k1_relat_1(sK1),k1_xboole_0))) ) ),
    inference(resolution,[],[f860,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f79,f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f860,plain,(
    ! [X5] :
      ( ~ r1_tarski(k6_subset_1(X5,k1_relat_1(sK1)),k1_xboole_0)
      | r1_tarski(X5,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f165,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f165,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1))
      | ~ r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),X2) ) ),
    inference(resolution,[],[f116,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f116,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X1,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f87,f98])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f80,f56,f57])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (16844)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (16837)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (16835)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16849)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (16854)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (16846)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (16843)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (16838)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (16833)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16832)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (16831)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (16834)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (16857)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (16853)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (16856)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (16852)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (16855)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (16845)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (16848)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (16839)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (16842)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (16836)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (16847)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (16840)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (16859)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (16860)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (16858)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (16850)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (16851)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (16841)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.92/0.63  % (16852)Refutation found. Thanks to Tanya!
% 1.92/0.63  % SZS status Theorem for theBenchmark
% 1.92/0.64  % SZS output start Proof for theBenchmark
% 1.92/0.64  fof(f930,plain,(
% 1.92/0.64    $false),
% 1.92/0.64    inference(subsumption_resolution,[],[f929,f46])).
% 1.92/0.64  fof(f46,plain,(
% 1.92/0.64    v1_relat_1(sK0)),
% 1.92/0.64    inference(cnf_transformation,[],[f27])).
% 1.92/0.64  fof(f27,plain,(
% 1.92/0.64    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.92/0.64    inference(flattening,[],[f26])).
% 1.92/0.64  fof(f26,plain,(
% 1.92/0.64    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.92/0.64    inference(ennf_transformation,[],[f24])).
% 1.92/0.64  fof(f24,negated_conjecture,(
% 1.92/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.92/0.64    inference(negated_conjecture,[],[f23])).
% 1.92/0.64  fof(f23,conjecture,(
% 1.92/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.92/0.64  fof(f929,plain,(
% 1.92/0.64    ~v1_relat_1(sK0)),
% 1.92/0.64    inference(subsumption_resolution,[],[f928,f44])).
% 1.92/0.64  fof(f44,plain,(
% 1.92/0.64    r1_tarski(sK0,sK1)),
% 1.92/0.64    inference(cnf_transformation,[],[f27])).
% 1.92/0.64  fof(f928,plain,(
% 1.92/0.64    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 1.92/0.64    inference(subsumption_resolution,[],[f926,f43])).
% 1.92/0.64  fof(f43,plain,(
% 1.92/0.64    v1_relat_1(sK1)),
% 1.92/0.64    inference(cnf_transformation,[],[f27])).
% 1.92/0.64  fof(f926,plain,(
% 1.92/0.64    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0)),
% 1.92/0.64    inference(resolution,[],[f912,f52])).
% 1.92/0.64  fof(f52,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f31])).
% 1.92/0.64  fof(f31,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.92/0.64    inference(flattening,[],[f30])).
% 1.92/0.64  fof(f30,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.92/0.64    inference(ennf_transformation,[],[f22])).
% 1.92/0.64  fof(f22,axiom,(
% 1.92/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.92/0.64  fof(f912,plain,(
% 1.92/0.64    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.92/0.64    inference(resolution,[],[f911,f117])).
% 1.92/0.64  fof(f117,plain,(
% 1.92/0.64    ( ! [X2] : (r1_tarski(X2,k3_relat_1(sK1)) | ~r1_tarski(X2,k2_relat_1(sK1))) )),
% 1.92/0.64    inference(superposition,[],[f85,f98])).
% 1.92/0.64  fof(f98,plain,(
% 1.92/0.64    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 1.92/0.64    inference(resolution,[],[f43,f83])).
% 1.92/0.64  fof(f83,plain,(
% 1.92/0.64    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.92/0.64    inference(definition_unfolding,[],[f49,f57])).
% 1.92/0.64  fof(f57,plain,(
% 1.92/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f14])).
% 1.92/0.64  fof(f14,axiom,(
% 1.92/0.64    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.92/0.64  fof(f49,plain,(
% 1.92/0.64    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f28])).
% 1.92/0.64  fof(f28,plain,(
% 1.92/0.64    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.92/0.64    inference(ennf_transformation,[],[f20])).
% 1.92/0.64  fof(f20,axiom,(
% 1.92/0.64    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.92/0.64  fof(f85,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.92/0.64    inference(definition_unfolding,[],[f78,f57])).
% 1.92/0.64  fof(f78,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f36])).
% 1.92/0.64  fof(f36,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.92/0.64    inference(ennf_transformation,[],[f4])).
% 1.92/0.64  fof(f4,axiom,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.92/0.64  fof(f911,plain,(
% 1.92/0.64    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 1.92/0.64    inference(subsumption_resolution,[],[f910,f45])).
% 1.92/0.64  fof(f45,plain,(
% 1.92/0.64    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.92/0.64    inference(cnf_transformation,[],[f27])).
% 1.92/0.64  fof(f910,plain,(
% 1.92/0.64    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.92/0.64    inference(subsumption_resolution,[],[f907,f44])).
% 1.92/0.64  fof(f907,plain,(
% 1.92/0.64    ~r1_tarski(sK0,sK1) | ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.92/0.64    inference(resolution,[],[f896,f122])).
% 1.92/0.64  fof(f122,plain,(
% 1.92/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),X0)) )),
% 1.92/0.64    inference(superposition,[],[f88,f100])).
% 1.92/0.64  fof(f100,plain,(
% 1.92/0.64    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 1.92/0.64    inference(resolution,[],[f46,f83])).
% 1.92/0.64  fof(f88,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.92/0.64    inference(definition_unfolding,[],[f82,f57])).
% 1.92/0.64  fof(f82,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f42])).
% 1.92/0.64  fof(f42,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.92/0.64    inference(flattening,[],[f41])).
% 1.92/0.64  fof(f41,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.92/0.64    inference(ennf_transformation,[],[f11])).
% 1.92/0.64  fof(f11,axiom,(
% 1.92/0.64    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.92/0.64  fof(f896,plain,(
% 1.92/0.64    ( ! [X7] : (r1_tarski(k1_relat_1(X7),k3_relat_1(sK1)) | ~r1_tarski(X7,sK1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f895,f103])).
% 1.92/0.64  fof(f103,plain,(
% 1.92/0.64    ( ! [X0] : (v1_relat_1(X0) | ~r1_tarski(X0,sK1)) )),
% 1.92/0.64    inference(resolution,[],[f97,f74])).
% 1.92/0.64  fof(f74,plain,(
% 1.92/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f17])).
% 1.92/0.64  fof(f17,axiom,(
% 1.92/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.92/0.64  fof(f97,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v1_relat_1(X0)) )),
% 1.92/0.64    inference(resolution,[],[f43,f53])).
% 1.92/0.64  fof(f53,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f32])).
% 1.92/0.64  fof(f32,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.92/0.64    inference(ennf_transformation,[],[f18])).
% 1.92/0.64  fof(f18,axiom,(
% 1.92/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.92/0.64  fof(f895,plain,(
% 1.92/0.64    ( ! [X7] : (r1_tarski(k1_relat_1(X7),k3_relat_1(sK1)) | ~r1_tarski(X7,sK1) | ~v1_relat_1(X7)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f892,f43])).
% 1.92/0.64  fof(f892,plain,(
% 1.92/0.64    ( ! [X7] : (r1_tarski(k1_relat_1(X7),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(X7,sK1) | ~v1_relat_1(X7)) )),
% 1.92/0.64    inference(resolution,[],[f875,f51])).
% 1.92/0.64  fof(f51,plain,(
% 1.92/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f31])).
% 1.92/0.64  fof(f875,plain,(
% 1.92/0.64    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 1.92/0.64    inference(resolution,[],[f873,f85])).
% 1.92/0.64  fof(f873,plain,(
% 1.92/0.64    ( ! [X0] : (~r1_tarski(X0,k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK1)))) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 1.92/0.64    inference(forward_demodulation,[],[f871,f55])).
% 1.92/0.64  fof(f55,plain,(
% 1.92/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f12])).
% 1.92/0.64  fof(f12,axiom,(
% 1.92/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.92/0.64  fof(f871,plain,(
% 1.92/0.64    ( ! [X0] : (r1_tarski(X0,k3_relat_1(sK1)) | ~r1_tarski(X0,k3_tarski(k2_tarski(k1_relat_1(sK1),k1_xboole_0)))) )),
% 1.92/0.64    inference(resolution,[],[f860,f86])).
% 1.92/0.64  fof(f86,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 1.92/0.64    inference(definition_unfolding,[],[f79,f57,f56])).
% 1.92/0.64  fof(f56,plain,(
% 1.92/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f16])).
% 1.92/0.64  fof(f16,axiom,(
% 1.92/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.92/0.64  fof(f79,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f37])).
% 1.92/0.64  fof(f37,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.92/0.64    inference(ennf_transformation,[],[f8])).
% 1.92/0.64  fof(f8,axiom,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.92/0.64  fof(f860,plain,(
% 1.92/0.64    ( ! [X5] : (~r1_tarski(k6_subset_1(X5,k1_relat_1(sK1)),k1_xboole_0) | r1_tarski(X5,k3_relat_1(sK1))) )),
% 1.92/0.64    inference(resolution,[],[f165,f48])).
% 1.92/0.64  fof(f48,plain,(
% 1.92/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f6])).
% 1.92/0.64  fof(f6,axiom,(
% 1.92/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.92/0.64  fof(f165,plain,(
% 1.92/0.64    ( ! [X2,X1] : (~r1_tarski(X2,k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1)) | ~r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),X2)) )),
% 1.92/0.64    inference(resolution,[],[f116,f81])).
% 1.92/0.64  fof(f81,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f40])).
% 1.92/0.64  fof(f40,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.92/0.64    inference(flattening,[],[f39])).
% 1.92/0.64  fof(f39,plain,(
% 1.92/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.92/0.64    inference(ennf_transformation,[],[f5])).
% 1.92/0.64  fof(f5,axiom,(
% 1.92/0.64    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.92/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.92/0.65  fof(f116,plain,(
% 1.92/0.65    ( ! [X1] : (~r1_tarski(k6_subset_1(X1,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X1,k3_relat_1(sK1))) )),
% 1.92/0.65    inference(superposition,[],[f87,f98])).
% 1.92/0.65  fof(f87,plain,(
% 1.92/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 1.92/0.65    inference(definition_unfolding,[],[f80,f56,f57])).
% 1.92/0.65  fof(f80,plain,(
% 1.92/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.92/0.65    inference(cnf_transformation,[],[f38])).
% 1.92/0.65  fof(f38,plain,(
% 1.92/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.92/0.65    inference(ennf_transformation,[],[f9])).
% 1.92/0.65  fof(f9,axiom,(
% 1.92/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.92/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.92/0.65  % SZS output end Proof for theBenchmark
% 1.92/0.65  % (16852)------------------------------
% 1.92/0.65  % (16852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.65  % (16852)Termination reason: Refutation
% 1.92/0.65  
% 1.92/0.65  % (16852)Memory used [KB]: 2174
% 1.92/0.65  % (16852)Time elapsed: 0.223 s
% 1.92/0.65  % (16852)------------------------------
% 1.92/0.65  % (16852)------------------------------
% 1.92/0.65  % (16830)Success in time 0.285 s
%------------------------------------------------------------------------------
