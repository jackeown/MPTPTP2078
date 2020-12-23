%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:30 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 244 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 ( 490 expanded)
%              Number of equality atoms :   37 ( 142 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(resolution,[],[f674,f262])).

fof(f262,plain,(
    ~ v1_tops_2(k9_subset_1(sK1,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f256,f76])).

fof(f76,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

% (10084)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f256,plain,(
    ~ v1_tops_2(k9_subset_1(sK1,sK2,sK1),sK0) ),
    inference(backward_demodulation,[],[f30,f249])).

fof(f249,plain,(
    ! [X6] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X6) = k9_subset_1(sK1,X6,sK1) ),
    inference(backward_demodulation,[],[f78,f248])).

fof(f248,plain,(
    ! [X27] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X27,sK1) = k9_subset_1(sK1,X27,sK1) ),
    inference(forward_demodulation,[],[f246,f235])).

fof(f235,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(resolution,[],[f58,f61])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

% (10073)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f246,plain,(
    ! [X27] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X27,sK1) = k1_setfam_1(k6_enumset1(X27,X27,X27,X27,X27,X27,X27,sK1)) ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

fof(f78,plain,(
    ! [X6] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X6,sK1) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X6) ),
    inference(resolution,[],[f47,f31])).

fof(f30,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f674,plain,(
    ! [X0] : v1_tops_2(k9_subset_1(sK1,sK1,X0),sK0) ),
    inference(subsumption_resolution,[],[f666,f297])).

fof(f297,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f261,f76])).

fof(f261,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f104,f249])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f45,f78])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f666,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(sK1,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(k9_subset_1(sK1,sK1,X0),sK0) ) ),
    inference(resolution,[],[f664,f91])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k9_subset_1(X0,X0,X1),X0) ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f86,plain,(
    ! [X4,X3] : r2_hidden(k9_subset_1(X3,X3,X4),k1_zfmisc_1(X3)) ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f84,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X3))
      | r2_hidden(k9_subset_1(X3,X3,X4),k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f82,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X0,X1),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f80,f61])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f45,f76])).

fof(f664,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f663,f31])).

fof(f663,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f385,f29])).

fof(f29,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f385,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK0) ) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_2(X2,X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:47:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (10067)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (10085)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (10077)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (10083)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (10075)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (10065)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (10083)Refutation not found, incomplete strategy% (10083)------------------------------
% 0.22/0.55  % (10083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10069)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (10083)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10083)Memory used [KB]: 10746
% 0.22/0.56  % (10083)Time elapsed: 0.130 s
% 0.22/0.56  % (10083)------------------------------
% 0.22/0.56  % (10083)------------------------------
% 0.22/0.56  % (10089)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.56  % (10076)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.56  % (10066)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.57  % (10067)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f676,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(resolution,[],[f674,f262])).
% 1.36/0.57  fof(f262,plain,(
% 1.36/0.57    ~v1_tops_2(k9_subset_1(sK1,sK1,sK2),sK0)),
% 1.36/0.57    inference(forward_demodulation,[],[f256,f76])).
% 1.36/0.57  fof(f76,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)) )),
% 1.36/0.57    inference(resolution,[],[f47,f61])).
% 1.36/0.57  fof(f61,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(forward_demodulation,[],[f35,f34])).
% 1.36/0.57  fof(f34,plain,(
% 1.36/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.57    inference(cnf_transformation,[],[f9])).
% 1.36/0.57  fof(f9,axiom,(
% 1.36/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.36/0.57  fof(f35,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f10])).
% 1.36/0.57  fof(f10,axiom,(
% 1.36/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.36/0.57  fof(f47,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f27])).
% 1.36/0.57  fof(f27,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f8])).
% 1.36/0.57  fof(f8,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.36/0.57  % (10084)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.57  fof(f256,plain,(
% 1.36/0.57    ~v1_tops_2(k9_subset_1(sK1,sK2,sK1),sK0)),
% 1.36/0.57    inference(backward_demodulation,[],[f30,f249])).
% 1.36/0.57  fof(f249,plain,(
% 1.36/0.57    ( ! [X6] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X6) = k9_subset_1(sK1,X6,sK1)) )),
% 1.36/0.57    inference(backward_demodulation,[],[f78,f248])).
% 1.36/0.57  fof(f248,plain,(
% 1.36/0.57    ( ! [X27] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X27,sK1) = k9_subset_1(sK1,X27,sK1)) )),
% 1.36/0.57    inference(forward_demodulation,[],[f246,f235])).
% 1.36/0.57  fof(f235,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 1.36/0.57    inference(resolution,[],[f58,f61])).
% 1.36/0.57  fof(f58,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.36/0.57    inference(definition_unfolding,[],[f46,f57])).
% 1.36/0.57  fof(f57,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.36/0.57    inference(definition_unfolding,[],[f37,f56])).
% 1.36/0.57  fof(f56,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f38,f55])).
% 1.36/0.57  fof(f55,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f44,f54])).
% 1.36/0.57  fof(f54,plain,(
% 1.36/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f48,f53])).
% 1.36/0.57  fof(f53,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f49,f52])).
% 1.36/0.57  fof(f52,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.57    inference(definition_unfolding,[],[f50,f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f6])).
% 1.36/0.57  fof(f6,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.36/0.57  fof(f50,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f5])).
% 1.36/0.57  fof(f5,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.57  fof(f49,plain,(
% 1.36/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f4])).
% 1.36/0.57  fof(f4,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.57  fof(f48,plain,(
% 1.36/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f3])).
% 1.36/0.57  % (10073)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.57  fof(f44,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f2])).
% 1.36/0.57  fof(f2,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.57  fof(f38,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f1])).
% 1.36/0.57  fof(f1,axiom,(
% 1.36/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.57  fof(f37,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f14])).
% 1.36/0.57  fof(f14,axiom,(
% 1.36/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.57  fof(f46,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f26])).
% 1.36/0.57  fof(f26,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f13])).
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.36/0.57  fof(f246,plain,(
% 1.36/0.57    ( ! [X27] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X27,sK1) = k1_setfam_1(k6_enumset1(X27,X27,X27,X27,X27,X27,X27,sK1))) )),
% 1.36/0.57    inference(resolution,[],[f58,f31])).
% 1.36/0.57  fof(f31,plain,(
% 1.36/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.57    inference(cnf_transformation,[],[f20])).
% 1.36/0.57  fof(f20,plain,(
% 1.36/0.57    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.36/0.57    inference(flattening,[],[f19])).
% 1.36/0.57  fof(f19,plain,(
% 1.36/0.57    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f18])).
% 1.36/0.57  fof(f18,negated_conjecture,(
% 1.36/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.36/0.57    inference(negated_conjecture,[],[f17])).
% 1.36/0.57  fof(f17,conjecture,(
% 1.36/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).
% 1.36/0.57  fof(f78,plain,(
% 1.36/0.57    ( ! [X6] : (k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X6,sK1) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X6)) )),
% 1.36/0.57    inference(resolution,[],[f47,f31])).
% 1.36/0.57  fof(f30,plain,(
% 1.36/0.57    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 1.36/0.57    inference(cnf_transformation,[],[f20])).
% 1.36/0.57  fof(f674,plain,(
% 1.36/0.57    ( ! [X0] : (v1_tops_2(k9_subset_1(sK1,sK1,X0),sK0)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f666,f297])).
% 1.36/0.57  fof(f297,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k9_subset_1(sK1,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.36/0.57    inference(superposition,[],[f261,f76])).
% 1.36/0.57  fof(f261,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k9_subset_1(sK1,X0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.36/0.57    inference(backward_demodulation,[],[f104,f249])).
% 1.36/0.57  fof(f104,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f99,f31])).
% 1.36/0.57  fof(f99,plain,(
% 1.36/0.57    ( ! [X0] : (m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.36/0.57    inference(superposition,[],[f45,f78])).
% 1.36/0.57  fof(f45,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f25])).
% 1.36/0.57  fof(f25,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.36/0.57    inference(ennf_transformation,[],[f11])).
% 1.36/0.57  fof(f11,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.36/0.57  fof(f666,plain,(
% 1.36/0.57    ( ! [X0] : (~m1_subset_1(k9_subset_1(sK1,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k9_subset_1(sK1,sK1,X0),sK0)) )),
% 1.36/0.57    inference(resolution,[],[f664,f91])).
% 1.36/0.57  fof(f91,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X0,X0,X1),X0)) )),
% 1.36/0.57    inference(resolution,[],[f86,f59])).
% 1.36/0.57  fof(f59,plain,(
% 1.36/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.36/0.57    inference(equality_resolution,[],[f41])).
% 1.36/0.57  fof(f41,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f7])).
% 1.36/0.57  fof(f7,axiom,(
% 1.36/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.36/0.57  fof(f86,plain,(
% 1.36/0.57    ( ! [X4,X3] : (r2_hidden(k9_subset_1(X3,X3,X4),k1_zfmisc_1(X3))) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f84,f33])).
% 1.36/0.57  fof(f33,plain,(
% 1.36/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(cnf_transformation,[],[f12])).
% 1.36/0.57  fof(f12,axiom,(
% 1.36/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.36/0.57  fof(f84,plain,(
% 1.36/0.57    ( ! [X4,X3] : (v1_xboole_0(k1_zfmisc_1(X3)) | r2_hidden(k9_subset_1(X3,X3,X4),k1_zfmisc_1(X3))) )),
% 1.36/0.57    inference(resolution,[],[f82,f39])).
% 1.36/0.57  fof(f39,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.36/0.57    inference(flattening,[],[f23])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f15])).
% 1.36/0.57  fof(f15,axiom,(
% 1.36/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.36/0.57  fof(f82,plain,(
% 1.36/0.57    ( ! [X0,X1] : (m1_subset_1(k9_subset_1(X0,X0,X1),k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f80,f61])).
% 1.36/0.57  fof(f80,plain,(
% 1.36/0.57    ( ! [X0,X1] : (m1_subset_1(k9_subset_1(X0,X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.36/0.57    inference(superposition,[],[f45,f76])).
% 1.36/0.57  fof(f664,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f663,f31])).
% 1.36/0.57  fof(f663,plain,(
% 1.36/0.57    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 1.36/0.57    inference(resolution,[],[f385,f29])).
% 1.36/0.57  fof(f29,plain,(
% 1.36/0.57    v1_tops_2(sK1,sK0)),
% 1.36/0.57    inference(cnf_transformation,[],[f20])).
% 1.36/0.57  fof(f385,plain,(
% 1.36/0.57    ( ! [X0,X1] : (~v1_tops_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) )),
% 1.36/0.57    inference(resolution,[],[f36,f32])).
% 1.36/0.57  fof(f32,plain,(
% 1.36/0.57    l1_pre_topc(sK0)),
% 1.36/0.57    inference(cnf_transformation,[],[f20])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,X2) | ~v1_tops_2(X2,X0) | v1_tops_2(X1,X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f22])).
% 1.36/0.57  fof(f22,plain,(
% 1.36/0.57    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.36/0.57    inference(flattening,[],[f21])).
% 1.36/0.57  fof(f21,plain,(
% 1.36/0.57    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f16])).
% 1.36/0.57  fof(f16,axiom,(
% 1.36/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
% 1.36/0.57  % SZS output end Proof for theBenchmark
% 1.36/0.57  % (10067)------------------------------
% 1.36/0.57  % (10067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (10067)Termination reason: Refutation
% 1.36/0.57  
% 1.36/0.57  % (10067)Memory used [KB]: 6652
% 1.36/0.57  % (10067)Time elapsed: 0.145 s
% 1.36/0.57  % (10067)------------------------------
% 1.36/0.57  % (10067)------------------------------
% 1.36/0.57  % (10061)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.58  % (10060)Success in time 0.212 s
%------------------------------------------------------------------------------
