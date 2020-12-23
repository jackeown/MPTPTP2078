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
% DateTime   : Thu Dec  3 13:15:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 303 expanded)
%              Number of leaves         :   12 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  214 (1154 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(resolution,[],[f88,f35])).

fof(f35,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f88,plain,(
    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(resolution,[],[f86,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f34,f49])).

fof(f49,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f46,f50])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    inference(resolution,[],[f81,f74])).

fof(f74,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f69,f54])).

fof(f54,plain,(
    m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f53,f49])).

fof(f53,plain,(
    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).

fof(f69,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f60,f66])).

fof(f66,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) ),
    inference(resolution,[],[f64,f33])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_tops_1(sK2(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(forward_demodulation,[],[f62,f49])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f59,f49])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f58,f49])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(k2_struct_0(sK0),sK0,X0) ) ),
    inference(superposition,[],[f80,f57])).

fof(f57,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(X0,sK0,X1) ) ),
    inference(resolution,[],[f79,f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(forward_demodulation,[],[f78,f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(forward_demodulation,[],[f77,f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m2_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:35:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (16193)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.46  % (16209)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.47  % (16201)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (16214)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.49  % (16201)Refutation not found, incomplete strategy% (16201)------------------------------
% 0.22/0.49  % (16201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16201)Memory used [KB]: 10618
% 0.22/0.49  % (16201)Time elapsed: 0.085 s
% 0.22/0.49  % (16201)------------------------------
% 0.22/0.49  % (16201)------------------------------
% 0.22/0.49  % (16198)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (16198)Refutation not found, incomplete strategy% (16198)------------------------------
% 0.22/0.49  % (16198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16198)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16198)Memory used [KB]: 6140
% 0.22/0.49  % (16198)Time elapsed: 0.062 s
% 0.22/0.49  % (16198)------------------------------
% 0.22/0.49  % (16198)------------------------------
% 0.22/0.49  % (16194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.49  % (16214)Refutation not found, incomplete strategy% (16214)------------------------------
% 0.22/0.49  % (16214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16214)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16214)Memory used [KB]: 10618
% 0.22/0.49  % (16214)Time elapsed: 0.067 s
% 0.22/0.49  % (16214)------------------------------
% 0.22/0.49  % (16214)------------------------------
% 0.22/0.49  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.22/0.49  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16194)Memory used [KB]: 10618
% 0.22/0.49  % (16194)Time elapsed: 0.077 s
% 0.22/0.49  % (16194)------------------------------
% 0.22/0.49  % (16194)------------------------------
% 0.22/0.49  % (16192)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (16200)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (16205)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (16196)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (16200)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f88,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f86,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f34,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f36,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f37,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f82,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f46,f50])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f81,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(resolution,[],[f69,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(forward_demodulation,[],[f53,f49])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(resolution,[],[f40,f33])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : ((v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_tops_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(superposition,[],[f60,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))),
% 0.22/0.50    inference(resolution,[],[f65,f54])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))),
% 0.22/0.50    inference(resolution,[],[f64,f33])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    inference(resolution,[],[f63,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (v1_tops_1(sK2(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f62,f49])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f38,f33])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f59,f49])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f58,f49])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f45,f33])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,X0)) )),
% 0.22/0.50    inference(superposition,[],[f80,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f56,f33])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f42,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(X0,sK0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f79,f33])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f78,f49])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f77,f49])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m2_connsp_2(X1,sK0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f44,f32])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (16200)------------------------------
% 0.22/0.50  % (16200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16200)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (16200)Memory used [KB]: 1663
% 0.22/0.50  % (16200)Time elapsed: 0.094 s
% 0.22/0.50  % (16200)------------------------------
% 0.22/0.50  % (16200)------------------------------
% 0.22/0.51  % (16191)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (16190)Success in time 0.137 s
%------------------------------------------------------------------------------
