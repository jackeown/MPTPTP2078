%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 620 expanded)
%              Number of leaves         :   19 ( 169 expanded)
%              Depth                    :   20
%              Number of atoms          :  302 (2539 expanded)
%              Number of equality atoms :   90 ( 736 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f47,f49,f200,f48,f201,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f201,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

% (20927)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (20930)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f198,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f119,f196])).

fof(f196,plain,(
    sK1 = k2_tops_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f194,f164])).

fof(f164,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f158,f147])).

fof(f147,plain,(
    ! [X2] : k3_subset_1(X2,k1_xboole_0) = X2 ),
    inference(backward_demodulation,[],[f134,f144])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f143,f129])).

fof(f129,plain,(
    ! [X4] : r1_tarski(k4_xboole_0(X4,X4),X4) ),
    inference(resolution,[],[f91,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f87,f89])).

% (20936)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f89,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f65,f76])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f143,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,X0),X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f83,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f134,plain,(
    ! [X2] : k3_subset_1(X2,k4_xboole_0(X2,X2)) = X2 ),
    inference(forward_demodulation,[],[f133,f62])).

fof(f133,plain,(
    ! [X2] : k3_subset_1(X2,k4_xboole_0(X2,X2)) = k3_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f127,f64])).

fof(f127,plain,(
    ! [X2] : k4_xboole_0(X2,k4_xboole_0(X2,X2)) = k3_subset_1(X2,k4_xboole_0(X2,X2)) ),
    inference(resolution,[],[f91,f66])).

fof(f158,plain,(
    ! [X2] : k3_subset_1(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f149,f66])).

fof(f149,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f91,f144])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f191,f92])).

fof(f92,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f191,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(superposition,[],[f125,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f114,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f102,plain,
    ( v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,
    ( v3_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

% (20932)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (20941)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (20927)Refutation not found, incomplete strategy% (20927)------------------------------
% (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20927)Termination reason: Refutation not found, incomplete strategy

% (20927)Memory used [KB]: 10746
% (20927)Time elapsed: 0.113 s
% (20927)------------------------------
% (20927)------------------------------
fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

% (20923)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f125,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f122,f105])).

fof(f105,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f48])).

fof(f103,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f122,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f108,f48])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f54,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f119,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f107,f48])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f61,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f200,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f51,f196])).

fof(f51,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f49,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

% (20926)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20921)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (20943)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (20919)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (20924)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (20920)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (20918)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (20917)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (20939)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (20929)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (20922)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (20929)Refutation not found, incomplete strategy% (20929)------------------------------
% 0.20/0.52  % (20929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20929)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20929)Memory used [KB]: 10746
% 0.20/0.52  % (20929)Time elapsed: 0.110 s
% 0.20/0.52  % (20929)------------------------------
% 0.20/0.52  % (20929)------------------------------
% 0.20/0.52  % (20924)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (20935)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (20940)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (20934)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f47,f49,f200,f48,f201,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f198,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  % (20927)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (20930)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f198,plain,(
% 0.20/0.52    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f119,f196])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f195])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    sK1 = k2_tops_1(sK0,sK1) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f194,f164])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.20/0.52    inference(forward_demodulation,[],[f158,f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X2] : (k3_subset_1(X2,k1_xboole_0) = X2) )),
% 0.20/0.52    inference(backward_demodulation,[],[f134,f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f143,f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X4] : (r1_tarski(k4_xboole_0(X4,X4),X4)) )),
% 0.20/0.52    inference(resolution,[],[f91,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(backward_demodulation,[],[f87,f89])).
% 0.20/0.52  % (20936)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X0] : (k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f66,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f65,f76])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,X0),X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(superposition,[],[f83,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f67,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ( ! [X2] : (k3_subset_1(X2,k4_xboole_0(X2,X2)) = X2) )),
% 0.20/0.52    inference(forward_demodulation,[],[f133,f62])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X2] : (k3_subset_1(X2,k4_xboole_0(X2,X2)) = k3_xboole_0(X2,X2)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f127,f64])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X2] : (k4_xboole_0(X2,k4_xboole_0(X2,X2)) = k3_subset_1(X2,k4_xboole_0(X2,X2))) )),
% 0.20/0.52    inference(resolution,[],[f91,f66])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    ( ! [X2] : (k3_subset_1(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f149,f66])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(backward_demodulation,[],[f91,f144])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f191,f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f73,f48])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(superposition,[],[f125,f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    k1_xboole_0 = k1_tops_1(sK0,sK1) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f114,f47])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    sK1 = k2_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f111,f48])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    sK1 = k2_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(resolution,[],[f102,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f101,f47])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f100,f48])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f56,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v3_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 0.20/0.52  % (20932)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (20941)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (20927)Refutation not found, incomplete strategy% (20927)------------------------------
% 0.20/0.52  % (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20927)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20927)Memory used [KB]: 10746
% 0.20/0.52  % (20927)Time elapsed: 0.113 s
% 0.20/0.52  % (20927)------------------------------
% 0.20/0.52  % (20927)------------------------------
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f37])).
% 0.20/0.52  % (20923)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f18])).
% 0.20/0.52  fof(f18,conjecture,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f122,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f104,f47])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f103,f48])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(resolution,[],[f55,f49])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.20/0.52    inference(resolution,[],[f108,f48])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.20/0.52    inference(resolution,[],[f54,f47])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f107,f48])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,k2_tops_1(sK0,X0)) | v2_tops_1(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f61,f47])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ~v3_tops_1(sK1,sK0)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f197])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    sK1 != sK1 | ~v3_tops_1(sK1,sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f51,f196])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~v3_tops_1(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    v4_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  % (20926)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20924)------------------------------
% 0.20/0.52  % (20924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20924)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (20924)Memory used [KB]: 1791
% 0.20/0.52  % (20924)Time elapsed: 0.099 s
% 0.20/0.52  % (20924)------------------------------
% 0.20/0.52  % (20924)------------------------------
% 0.20/0.53  % (20916)Success in time 0.165 s
%------------------------------------------------------------------------------
