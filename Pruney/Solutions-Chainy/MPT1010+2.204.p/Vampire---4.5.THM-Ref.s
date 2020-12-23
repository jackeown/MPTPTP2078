%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:19 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 295 expanded)
%              Number of equality atoms :   82 ( 145 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f25])).

fof(f25,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f102,plain,(
    sK1 = k1_funct_1(sK3,sK2) ),
    inference(resolution,[],[f101,f24])).

fof(f24,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,(
    ! [X43] :
      ( ~ r2_hidden(X43,sK0)
      | sK1 = k1_funct_1(sK3,X43) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X43] :
      ( sK1 = k1_funct_1(sK3,X43)
      | sK1 = k1_funct_1(sK3,X43)
      | sK1 = k1_funct_1(sK3,X43)
      | sK1 = k1_funct_1(sK3,X43)
      | sK1 = k1_funct_1(sK3,X43)
      | sK1 = k1_funct_1(sK3,X43)
      | ~ r2_hidden(X43,sK0) ) ),
    inference(resolution,[],[f73,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f91,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(subsumption_resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X7,X3,X1] : r2_hidden(X7,k4_enumset1(X0,X1,X2,X3,X4,X7)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X7) != X6 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f84,f30])).

fof(f30,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0)))) ) ),
    inference(subsumption_resolution,[],[f83,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)
      | ~ v1_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0)))
      | ~ r2_hidden(X0,k2_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0)))) ) ),
    inference(superposition,[],[f59,f82])).

fof(f82,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f81,f29])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f80,f30])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f31,f27])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f34,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f90,f21])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f22,f56])).

fof(f22,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
      | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f23,f56])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(X7,k4_enumset1(X0,X1,X2,X3,X4,X5))
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | X5 = X7
      | X0 = X7 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X7
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | X5 = X7
      | ~ r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:00:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (18197)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.53  % (18192)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.53  % (18205)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.54  % (18187)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.54  % (18189)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (18197)Refutation not found, incomplete strategy% (18197)------------------------------
% 0.23/0.54  % (18197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (18188)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.54  % (18213)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.54  % (18197)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (18197)Memory used [KB]: 10618
% 0.23/0.54  % (18197)Time elapsed: 0.115 s
% 0.23/0.54  % (18197)------------------------------
% 0.23/0.54  % (18197)------------------------------
% 0.23/0.54  % (18193)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.54  % (18193)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f104,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f102,f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f15,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.23/0.54    inference(flattening,[],[f14])).
% 0.23/0.54  fof(f14,plain,(
% 0.23/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.23/0.54    inference(ennf_transformation,[],[f13])).
% 0.23/0.54  fof(f13,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.23/0.54    inference(negated_conjecture,[],[f12])).
% 0.23/0.54  fof(f12,conjecture,(
% 0.23/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.23/0.54  fof(f102,plain,(
% 0.23/0.54    sK1 = k1_funct_1(sK3,sK2)),
% 0.23/0.54    inference(resolution,[],[f101,f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    r2_hidden(sK2,sK0)),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f101,plain,(
% 0.23/0.54    ( ! [X43] : (~r2_hidden(X43,sK0) | sK1 = k1_funct_1(sK3,X43)) )),
% 0.23/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.23/0.54  fof(f100,plain,(
% 0.23/0.54    ( ! [X43] : (sK1 = k1_funct_1(sK3,X43) | sK1 = k1_funct_1(sK3,X43) | sK1 = k1_funct_1(sK3,X43) | sK1 = k1_funct_1(sK3,X43) | sK1 = k1_funct_1(sK3,X43) | sK1 = k1_funct_1(sK3,X43) | ~r2_hidden(X43,sK0)) )),
% 0.23/0.54    inference(resolution,[],[f73,f92])).
% 0.23/0.54  fof(f92,plain,(
% 0.23/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,sK0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f91,f86])).
% 0.23/0.54  fof(f86,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f85,f62])).
% 0.23/0.54  fof(f62,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,k4_enumset1(X0,X1,X2,X3,X4,X7))) )),
% 0.23/0.54    inference(equality_resolution,[],[f61])).
% 0.23/0.54  fof(f61,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X7) != X6) )),
% 0.23/0.54    inference(equality_resolution,[],[f52])).
% 0.23/0.54  fof(f52,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  fof(f20,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 0.23/0.54    inference(ennf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 0.23/0.54  fof(f85,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X0,X0)) | k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.54    inference(forward_demodulation,[],[f84,f30])).
% 0.23/0.54  fof(f30,plain,(
% 0.23/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.54  fof(f84,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k2_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0))))) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f83,f27])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.54  fof(f83,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 != k4_enumset1(X0,X0,X0,X0,X0,X0) | ~v1_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0))) | ~r2_hidden(X0,k2_relat_1(k6_relat_1(k4_enumset1(X0,X0,X0,X0,X0,X0))))) )),
% 0.23/0.54    inference(superposition,[],[f59,f82])).
% 0.23/0.54  fof(f82,plain,(
% 0.23/0.54    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.23/0.54    inference(forward_demodulation,[],[f81,f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f81,plain,(
% 0.23/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.23/0.54    inference(forward_demodulation,[],[f80,f30])).
% 0.23/0.54  fof(f80,plain,(
% 0.23/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 0.23/0.54    inference(resolution,[],[f31,f27])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f16])).
% 0.23/0.54  fof(f16,plain,(
% 0.23/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.23/0.54  fof(f59,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.23/0.54    inference(definition_unfolding,[],[f34,f56])).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f26,f55])).
% 0.23/0.54  fof(f55,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f32,f54])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f35,f53])).
% 0.23/0.54  fof(f53,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.54    inference(definition_unfolding,[],[f36,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.54  fof(f36,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f17])).
% 0.23/0.54  fof(f17,plain,(
% 0.23/0.54    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.23/0.54  fof(f91,plain,(
% 0.23/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f90,f21])).
% 0.23/0.54  fof(f21,plain,(
% 0.23/0.54    v1_funct_1(sK3)),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f90,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.23/0.54    inference(subsumption_resolution,[],[f89,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    v1_funct_2(sK3,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.23/0.54    inference(definition_unfolding,[],[f22,f56])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f89,plain,(
% 0.23/0.54    ( ! [X0] : (~v1_funct_2(sK3,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | r2_hidden(k1_funct_1(sK3,X0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.23/0.54    inference(resolution,[],[f37,f57])).
% 0.23/0.54  fof(f57,plain,(
% 0.23/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.23/0.54    inference(definition_unfolding,[],[f23,f56])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.23/0.54    inference(cnf_transformation,[],[f15])).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.54    inference(flattening,[],[f18])).
% 0.23/0.54  fof(f18,plain,(
% 0.23/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.54    inference(ennf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.23/0.54  fof(f73,plain,(
% 0.23/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(X7,k4_enumset1(X0,X1,X2,X3,X4,X5)) | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | X0 = X7) )),
% 0.23/0.54    inference(equality_resolution,[],[f46])).
% 0.23/0.54  fof(f46,plain,(
% 0.23/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | ~r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.23/0.54    inference(cnf_transformation,[],[f20])).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (18193)------------------------------
% 0.23/0.54  % (18193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (18193)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (18193)Memory used [KB]: 6268
% 0.23/0.54  % (18193)Time elapsed: 0.125 s
% 0.23/0.54  % (18193)------------------------------
% 0.23/0.54  % (18193)------------------------------
% 0.23/0.54  % (18216)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.55  % (18186)Success in time 0.175 s
%------------------------------------------------------------------------------
