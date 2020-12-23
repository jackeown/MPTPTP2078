%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:36 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  133 (1087 expanded)
%              Number of leaves         :   20 ( 295 expanded)
%              Depth                    :   27
%              Number of atoms          :  334 (4783 expanded)
%              Number of equality atoms :   94 ( 438 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1813,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f738,f1795,f485])).

fof(f485,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f54,f483])).

fof(f483,plain,(
    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f482])).

fof(f482,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f480,f129])).

fof(f129,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f126,f82])).

fof(f82,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f64,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f126,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f62,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f74,f78])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f480,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f468,f155])).

fof(f155,plain,(
    ! [X5] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5) ),
    inference(resolution,[],[f109,f75])).

fof(f75,plain,(
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

fof(f109,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f90,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f468,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f124,f459])).

fof(f459,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f108,f458])).

fof(f458,plain,(
    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f450,f114])).

fof(f114,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f97,f52])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f56,f51])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f450,plain,(
    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f171,f52])).

fof(f171,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,sK1)) = k2_xboole_0(X4,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f110,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f110,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f91,f52])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f108,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f94,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f93,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f92,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f124,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f101,f52])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f57,f51])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f54,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1795,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1766])).

fof(f1766,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f111,f1764])).

fof(f1764,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1762,f139])).

fof(f139,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f136,f83])).

fof(f136,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k3_xboole_0(X4,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f84,f82])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f62,f62])).

fof(f1762,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(resolution,[],[f1685,f64])).

fof(f1685,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1684,f133])).

fof(f133,plain,(
    ! [X4] :
      ( k1_xboole_0 != X4
      | r1_tarski(X4,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f132,f83])).

fof(f132,plain,(
    ! [X4] :
      ( k1_xboole_0 != X4
      | r1_tarski(X4,k4_xboole_0(X4,X4)) ) ),
    inference(superposition,[],[f85,f82])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f73,f62])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1684,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1683,f1481])).

fof(f1481,plain,(
    k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1471,f83])).

fof(f1471,plain,(
    k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f62,f565])).

fof(f565,plain,(
    k2_pre_topc(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f367,f483])).

fof(f367,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f155,f124])).

fof(f1683,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1682,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1682,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1669,f139])).

fof(f1669,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0)
    | r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f138,f559])).

fof(f559,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f357,f483])).

fof(f357,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f182,f74])).

fof(f182,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f104,f103])).

fof(f103,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f88,f52])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f55,f51])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,k2_tops_1(sK0,sK1))
      | k1_xboole_0 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f94,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f138,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X2,k4_xboole_0(X2,X3))
      | r1_tarski(X2,k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f73,f84])).

fof(f111,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f95,f52])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 != k1_tops_1(sK0,X0)
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f738,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f732,f691])).

fof(f691,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f686,f492])).

fof(f492,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f114,f483])).

fof(f686,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f153,f52])).

fof(f153,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),X3)) ) ),
    inference(resolution,[],[f109,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f732,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f151,f52])).

fof(f151,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1)) ) ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (3803)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (3826)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (3810)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (3811)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (3805)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (3813)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.52  % (3819)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.53  % (3812)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.53  % (3827)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.22/0.53  % (3804)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.53  % (3829)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.53  % (3807)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.53  % (3822)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.53  % (3800)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (3809)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.53  % (3802)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (3801)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.54  % (3821)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (3824)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (3828)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (3823)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.54  % (3825)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (3814)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.55  % (3815)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.55  % (3816)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.55  % (3820)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.55  % (3817)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.55  % (3818)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (3808)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (3806)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.08/0.65  % (3803)Refutation not found, incomplete strategy% (3803)------------------------------
% 2.08/0.65  % (3803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (3803)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.65  
% 2.08/0.65  % (3803)Memory used [KB]: 6140
% 2.08/0.65  % (3803)Time elapsed: 0.219 s
% 2.08/0.65  % (3803)------------------------------
% 2.08/0.65  % (3803)------------------------------
% 2.08/0.66  % (3807)Refutation found. Thanks to Tanya!
% 2.08/0.66  % SZS status Theorem for theBenchmark
% 2.08/0.66  % SZS output start Proof for theBenchmark
% 2.08/0.66  fof(f1813,plain,(
% 2.08/0.66    $false),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f738,f1795,f485])).
% 2.08/0.66  fof(f485,plain,(
% 2.08/0.66    ~v2_tops_1(sK1,sK0) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.08/0.66    inference(backward_demodulation,[],[f54,f483])).
% 2.08/0.66  fof(f483,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(duplicate_literal_removal,[],[f482])).
% 2.08/0.66  fof(f482,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(forward_demodulation,[],[f480,f129])).
% 2.08/0.66  fof(f129,plain,(
% 2.08/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.66    inference(forward_demodulation,[],[f126,f82])).
% 2.08/0.66  fof(f82,plain,(
% 2.08/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.08/0.66    inference(resolution,[],[f64,f78])).
% 2.08/0.66  fof(f78,plain,(
% 2.08/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.08/0.66    inference(equality_resolution,[],[f71])).
% 2.08/0.66  fof(f71,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.08/0.66    inference(cnf_transformation,[],[f49])).
% 2.08/0.66  fof(f49,plain,(
% 2.08/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.66    inference(flattening,[],[f48])).
% 2.08/0.66  fof(f48,plain,(
% 2.08/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.08/0.66    inference(nnf_transformation,[],[f2])).
% 2.08/0.66  fof(f2,axiom,(
% 2.08/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.08/0.66  fof(f64,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f29])).
% 2.08/0.66  fof(f29,plain,(
% 2.08/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.08/0.66    inference(ennf_transformation,[],[f6])).
% 2.08/0.66  fof(f6,axiom,(
% 2.08/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.08/0.66  fof(f126,plain,(
% 2.08/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.08/0.66    inference(superposition,[],[f62,f83])).
% 2.08/0.66  fof(f83,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.08/0.66    inference(resolution,[],[f74,f78])).
% 2.08/0.66  fof(f74,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f50])).
% 2.08/0.66  fof(f50,plain,(
% 2.08/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.08/0.66    inference(nnf_transformation,[],[f3])).
% 2.08/0.66  fof(f3,axiom,(
% 2.08/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.08/0.66  fof(f62,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f7])).
% 2.08/0.66  fof(f7,axiom,(
% 2.08/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.08/0.66  fof(f480,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(superposition,[],[f468,f155])).
% 2.08/0.66  fof(f155,plain,(
% 2.08/0.66    ( ! [X5] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5)) )),
% 2.08/0.66    inference(resolution,[],[f109,f75])).
% 2.08/0.66  fof(f75,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f36])).
% 2.08/0.66  fof(f36,plain,(
% 2.08/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f9])).
% 2.08/0.66  fof(f9,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.08/0.66  fof(f109,plain,(
% 2.08/0.66    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.66    inference(resolution,[],[f90,f52])).
% 2.08/0.66  fof(f52,plain,(
% 2.08/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.66    inference(cnf_transformation,[],[f45])).
% 2.08/0.66  fof(f45,plain,(
% 2.08/0.66    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.08/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.08/0.66  fof(f43,plain,(
% 2.08/0.66    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.08/0.66    introduced(choice_axiom,[])).
% 2.08/0.66  fof(f44,plain,(
% 2.08/0.66    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.08/0.66    introduced(choice_axiom,[])).
% 2.08/0.66  fof(f42,plain,(
% 2.08/0.66    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.08/0.66    inference(flattening,[],[f41])).
% 2.08/0.66  fof(f41,plain,(
% 2.08/0.66    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.08/0.66    inference(nnf_transformation,[],[f21])).
% 2.08/0.66  fof(f21,plain,(
% 2.08/0.66    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f20])).
% 2.08/0.66  fof(f20,negated_conjecture,(
% 2.08/0.66    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.08/0.66    inference(negated_conjecture,[],[f19])).
% 2.08/0.66  fof(f19,conjecture,(
% 2.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 2.08/0.66  fof(f90,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.08/0.66    inference(resolution,[],[f68,f51])).
% 2.08/0.66  fof(f51,plain,(
% 2.08/0.66    l1_pre_topc(sK0)),
% 2.08/0.66    inference(cnf_transformation,[],[f45])).
% 2.08/0.66  fof(f68,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f33])).
% 2.08/0.66  fof(f33,plain,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(flattening,[],[f32])).
% 2.08/0.66  fof(f32,plain,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f12])).
% 2.08/0.66  fof(f12,axiom,(
% 2.08/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.08/0.66  fof(f468,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(superposition,[],[f124,f459])).
% 2.08/0.66  fof(f459,plain,(
% 2.08/0.66    k1_xboole_0 = k1_tops_1(sK0,sK1) | k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(backward_demodulation,[],[f108,f458])).
% 2.08/0.66  fof(f458,plain,(
% 2.08/0.66    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 2.08/0.66    inference(forward_demodulation,[],[f450,f114])).
% 2.08/0.66  fof(f114,plain,(
% 2.08/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f97,f52])).
% 2.08/0.66  fof(f97,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.08/0.66    inference(resolution,[],[f56,f51])).
% 2.08/0.66  fof(f56,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f23])).
% 2.08/0.66  fof(f23,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f17])).
% 2.08/0.66  fof(f17,axiom,(
% 2.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.08/0.66  fof(f450,plain,(
% 2.08/0.66    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f171,f52])).
% 2.08/0.66  fof(f171,plain,(
% 2.08/0.66    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,sK1)) = k2_xboole_0(X4,k2_tops_1(sK0,sK1))) )),
% 2.08/0.66    inference(resolution,[],[f110,f77])).
% 2.08/0.66  fof(f77,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f40])).
% 2.08/0.66  fof(f40,plain,(
% 2.08/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(flattening,[],[f39])).
% 2.08/0.66  fof(f39,plain,(
% 2.08/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.08/0.66    inference(ennf_transformation,[],[f8])).
% 2.08/0.66  fof(f8,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.08/0.66  fof(f110,plain,(
% 2.08/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.08/0.66    inference(resolution,[],[f91,f52])).
% 2.08/0.66  fof(f91,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.08/0.66    inference(resolution,[],[f69,f51])).
% 2.08/0.66  fof(f69,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f35])).
% 2.08/0.66  fof(f35,plain,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(flattening,[],[f34])).
% 2.08/0.66  fof(f34,plain,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f13])).
% 2.08/0.66  fof(f13,axiom,(
% 2.08/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.08/0.66  fof(f108,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(resolution,[],[f94,f63])).
% 2.08/0.66  fof(f63,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.08/0.66    inference(cnf_transformation,[],[f28])).
% 2.08/0.66  fof(f28,plain,(
% 2.08/0.66    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.08/0.66    inference(ennf_transformation,[],[f4])).
% 2.08/0.66  fof(f4,axiom,(
% 2.08/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.08/0.66  fof(f94,plain,(
% 2.08/0.66    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(subsumption_resolution,[],[f93,f51])).
% 2.08/0.66  fof(f93,plain,(
% 2.08/0.66    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(subsumption_resolution,[],[f92,f52])).
% 2.08/0.66  fof(f92,plain,(
% 2.08/0.66    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f58,f53])).
% 2.08/0.66  fof(f53,plain,(
% 2.08/0.66    v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(cnf_transformation,[],[f45])).
% 2.08/0.66  fof(f58,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f46])).
% 2.08/0.66  fof(f46,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(nnf_transformation,[],[f25])).
% 2.08/0.66  fof(f25,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f18])).
% 2.08/0.66  fof(f18,axiom,(
% 2.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 2.08/0.66  fof(f124,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f101,f52])).
% 2.08/0.66  fof(f101,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 2.08/0.66    inference(resolution,[],[f57,f51])).
% 2.08/0.66  fof(f57,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f24])).
% 2.08/0.66  fof(f24,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f14])).
% 2.08/0.66  fof(f14,axiom,(
% 2.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.08/0.66  fof(f54,plain,(
% 2.08/0.66    ~v2_tops_1(sK1,sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(cnf_transformation,[],[f45])).
% 2.08/0.66  fof(f1795,plain,(
% 2.08/0.66    v2_tops_1(sK1,sK0)),
% 2.08/0.66    inference(trivial_inequality_removal,[],[f1766])).
% 2.08/0.66  fof(f1766,plain,(
% 2.08/0.66    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0)),
% 2.08/0.66    inference(backward_demodulation,[],[f111,f1764])).
% 2.08/0.66  fof(f1764,plain,(
% 2.08/0.66    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(forward_demodulation,[],[f1762,f139])).
% 2.08/0.66  fof(f139,plain,(
% 2.08/0.66    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) )),
% 2.08/0.66    inference(forward_demodulation,[],[f136,f83])).
% 2.08/0.66  fof(f136,plain,(
% 2.08/0.66    ( ! [X4] : (k4_xboole_0(X4,X4) = k3_xboole_0(X4,k4_xboole_0(X4,X4))) )),
% 2.08/0.66    inference(superposition,[],[f84,f82])).
% 2.08/0.66  fof(f84,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(superposition,[],[f62,f62])).
% 2.08/0.66  fof(f1762,plain,(
% 2.08/0.66    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 2.08/0.66    inference(resolution,[],[f1685,f64])).
% 2.08/0.66  fof(f1685,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 2.08/0.66    inference(subsumption_resolution,[],[f1684,f133])).
% 2.08/0.66  fof(f133,plain,(
% 2.08/0.66    ( ! [X4] : (k1_xboole_0 != X4 | r1_tarski(X4,k1_xboole_0)) )),
% 2.08/0.66    inference(forward_demodulation,[],[f132,f83])).
% 2.08/0.66  fof(f132,plain,(
% 2.08/0.66    ( ! [X4] : (k1_xboole_0 != X4 | r1_tarski(X4,k4_xboole_0(X4,X4))) )),
% 2.08/0.66    inference(superposition,[],[f85,f82])).
% 2.08/0.66  fof(f85,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,k4_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(superposition,[],[f73,f62])).
% 2.08/0.66  fof(f73,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f50])).
% 2.08/0.66  fof(f1684,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(forward_demodulation,[],[f1683,f1481])).
% 2.08/0.66  fof(f1481,plain,(
% 2.08/0.66    k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.08/0.66    inference(forward_demodulation,[],[f1471,f83])).
% 2.08/0.66  fof(f1471,plain,(
% 2.08/0.66    k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.08/0.66    inference(superposition,[],[f62,f565])).
% 2.08/0.66  fof(f565,plain,(
% 2.08/0.66    k2_pre_topc(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.08/0.66    inference(backward_demodulation,[],[f367,f483])).
% 2.08/0.66  fof(f367,plain,(
% 2.08/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.08/0.66    inference(superposition,[],[f155,f124])).
% 2.08/0.66  fof(f1683,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(forward_demodulation,[],[f1682,f61])).
% 2.08/0.66  fof(f61,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f1])).
% 2.08/0.66  fof(f1,axiom,(
% 2.08/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.08/0.66  fof(f1682,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(subsumption_resolution,[],[f1669,f139])).
% 2.08/0.66  fof(f1669,plain,(
% 2.08/0.66    k1_xboole_0 != k3_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) | r1_tarski(k1_tops_1(sK0,sK1),k3_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(superposition,[],[f138,f559])).
% 2.08/0.66  fof(f559,plain,(
% 2.08/0.66    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(backward_demodulation,[],[f357,f483])).
% 2.08/0.66  fof(f357,plain,(
% 2.08/0.66    k1_xboole_0 = k1_tops_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.08/0.66    inference(resolution,[],[f182,f74])).
% 2.08/0.66  fof(f182,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.08/0.66    inference(resolution,[],[f104,f103])).
% 2.08/0.66  fof(f103,plain,(
% 2.08/0.66    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.08/0.66    inference(resolution,[],[f88,f52])).
% 2.08/0.66  fof(f88,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.08/0.66    inference(resolution,[],[f55,f51])).
% 2.08/0.66  fof(f55,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f22])).
% 2.08/0.66  fof(f22,plain,(
% 2.08/0.66    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f15])).
% 2.08/0.66  fof(f15,axiom,(
% 2.08/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.08/0.66  fof(f104,plain,(
% 2.08/0.66    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)) )),
% 2.08/0.66    inference(resolution,[],[f94,f76])).
% 2.08/0.66  fof(f76,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f38])).
% 2.08/0.66  fof(f38,plain,(
% 2.08/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.08/0.66    inference(flattening,[],[f37])).
% 2.08/0.66  fof(f37,plain,(
% 2.08/0.66    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.08/0.66    inference(ennf_transformation,[],[f5])).
% 2.08/0.66  fof(f5,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.08/0.66  fof(f138,plain,(
% 2.08/0.66    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X2,k4_xboole_0(X2,X3)) | r1_tarski(X2,k3_xboole_0(X2,X3))) )),
% 2.08/0.66    inference(superposition,[],[f73,f84])).
% 2.08/0.66  fof(f111,plain,(
% 2.08/0.66    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 2.08/0.66    inference(resolution,[],[f95,f52])).
% 2.08/0.66  fof(f95,plain,(
% 2.08/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,X0) | v2_tops_1(X0,sK0)) )),
% 2.08/0.66    inference(resolution,[],[f59,f51])).
% 2.08/0.66  fof(f59,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f46])).
% 2.08/0.66  fof(f738,plain,(
% 2.08/0.66    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.08/0.66    inference(subsumption_resolution,[],[f732,f691])).
% 2.08/0.66  fof(f691,plain,(
% 2.08/0.66    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.08/0.66    inference(forward_demodulation,[],[f686,f492])).
% 2.08/0.66  fof(f492,plain,(
% 2.08/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))),
% 2.08/0.66    inference(backward_demodulation,[],[f114,f483])).
% 2.08/0.66  fof(f686,plain,(
% 2.08/0.66    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.08/0.66    inference(resolution,[],[f153,f52])).
% 2.08/0.66  fof(f153,plain,(
% 2.08/0.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),X3))) )),
% 2.08/0.66    inference(resolution,[],[f109,f65])).
% 2.08/0.66  fof(f65,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f30])).
% 2.08/0.66  fof(f30,plain,(
% 2.08/0.66    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f11])).
% 2.08/0.66  fof(f11,axiom,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 2.08/0.66  fof(f732,plain,(
% 2.08/0.66    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.08/0.66    inference(resolution,[],[f151,f52])).
% 2.08/0.66  fof(f151,plain,(
% 2.08/0.66    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k2_pre_topc(sK0,sK1)) | ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),X1))) )),
% 2.08/0.66    inference(resolution,[],[f109,f67])).
% 2.08/0.66  fof(f67,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f47])).
% 2.08/0.66  fof(f47,plain,(
% 2.08/0.66    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(nnf_transformation,[],[f31])).
% 2.08/0.66  fof(f31,plain,(
% 2.08/0.66    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f10])).
% 2.08/0.66  fof(f10,axiom,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.08/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 2.08/0.66  % SZS output end Proof for theBenchmark
% 2.08/0.66  % (3807)------------------------------
% 2.08/0.66  % (3807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.66  % (3807)Termination reason: Refutation
% 2.08/0.66  
% 2.08/0.66  % (3807)Memory used [KB]: 2686
% 2.08/0.66  % (3807)Time elapsed: 0.241 s
% 2.08/0.66  % (3807)------------------------------
% 2.08/0.66  % (3807)------------------------------
% 2.08/0.67  % (3799)Success in time 0.301 s
%------------------------------------------------------------------------------
