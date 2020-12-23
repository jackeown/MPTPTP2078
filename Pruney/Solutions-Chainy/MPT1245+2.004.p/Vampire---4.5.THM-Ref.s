%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 291 expanded)
%              Number of leaves         :   13 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  156 ( 948 expanded)
%              Number of equality atoms :   59 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,(
    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f30,f70])).

fof(f70,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f69,f67])).

fof(f67,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f66,f49])).

fof(f49,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f28,f44])).

fof(f44,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1)))
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f66,plain,(
    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f56,f65])).

fof(f65,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f64,f45])).

fof(f64,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k3_subset_1(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f63,f47])).

fof(f47,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f39,f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f62,f29])).

fof(f29,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k4_xboole_0(k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) ) ),
    inference(forward_demodulation,[],[f61,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f61,plain,(
    ! [X0] :
      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f60,f44])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) ) ),
    inference(forward_demodulation,[],[f59,f44])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f37,f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v2_pre_topc(X0) )
            & ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (24461)Refutation not found, incomplete strategy% (24461)------------------------------
% (24461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24461)Termination reason: Refutation not found, incomplete strategy

% (24461)Memory used [KB]: 6140
% (24461)Time elapsed: 0.095 s
% (24461)------------------------------
% (24461)------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f56,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f54,f45])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f53,f44])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f52,f44])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f69,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) ) ),
    inference(forward_demodulation,[],[f57,f44])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) ) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

fof(f30,plain,(
    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (24462)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.47  % (24462)Refutation not found, incomplete strategy% (24462)------------------------------
% 0.20/0.47  % (24462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (24462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (24462)Memory used [KB]: 10618
% 0.20/0.47  % (24462)Time elapsed: 0.060 s
% 0.20/0.47  % (24462)------------------------------
% 0.20/0.47  % (24462)------------------------------
% 0.20/0.48  % (24459)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (24463)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (24461)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (24463)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)),
% 0.20/0.52    inference(superposition,[],[f30,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.20/0.52    inference(forward_demodulation,[],[f69,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f66,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.52    inference(resolution,[],[f40,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.52    inference(backward_demodulation,[],[f28,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f33,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f34,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    (k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1))) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X1] : (k2_pre_topc(sK0,X1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X1))) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f56,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    k3_subset_1(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.52    inference(resolution,[],[f64,f45])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.52    inference(forward_demodulation,[],[f63,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 0.20/0.52    inference(resolution,[],[f39,f45])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.20/0.52    inference(resolution,[],[f62,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v3_pre_topc(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f61,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 0.20/0.52    inference(resolution,[],[f41,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f32,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f60,f44])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f59,f44])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0))) )),
% 0.20/0.52    inference(resolution,[],[f37,f27])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0)) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v2_pre_topc(X0))) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  % (24461)Refutation not found, incomplete strategy% (24461)------------------------------
% 0.20/0.52  % (24461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24461)Memory used [KB]: 6140
% 0.20/0.52  % (24461)Time elapsed: 0.095 s
% 0.20/0.52  % (24461)------------------------------
% 0.20/0.52  % (24461)------------------------------
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.20/0.52    inference(resolution,[],[f54,f45])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f44])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f52,f44])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.20/0.52    inference(resolution,[],[f35,f27])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 0.20/0.52    inference(resolution,[],[f58,f45])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f57,f44])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))))) )),
% 0.20/0.52    inference(resolution,[],[f36,f27])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (24463)------------------------------
% 0.20/0.52  % (24463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24463)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (24463)Memory used [KB]: 1663
% 0.20/0.52  % (24463)Time elapsed: 0.079 s
% 0.20/0.52  % (24463)------------------------------
% 0.20/0.52  % (24463)------------------------------
% 0.20/0.52  % (24452)Success in time 0.161 s
%------------------------------------------------------------------------------
