%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:12 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 636 expanded)
%              Number of leaves         :   23 ( 183 expanded)
%              Depth                    :   20
%              Number of atoms          :  311 (2369 expanded)
%              Number of equality atoms :  118 ( 793 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f795,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f50,f49,f728,f51,f766,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f766,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f762,f51])).

fof(f762,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f746,f283])).

fof(f283,plain,(
    ! [X1] :
      ( k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f282,f146])).

fof(f146,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f282,plain,(
    ! [X1] :
      ( k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X1] :
      ( k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f243,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f243,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f746,plain,(
    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f468,f726])).

fof(f726,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f53,f170,f725])).

fof(f725,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f724,f50])).

fof(f724,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f720,f51])).

fof(f720,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f59,f237])).

fof(f237,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f234,f51])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f219,f170])).

fof(f219,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f170,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f152,f150])).

fof(f150,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) ),
    inference(resolution,[],[f84,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f57,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f76,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f152,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f52,f149])).

fof(f149,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f84,f51])).

fof(f52,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f53,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f468,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k7_subset_1(X11,X11,X12)) = X11 ),
    inference(resolution,[],[f448,f155])).

fof(f155,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f81,f150])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f448,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(forward_demodulation,[],[f427,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f427,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f124,f423])).

fof(f423,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f422,f206])).

fof(f206,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f162,f155])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(backward_demodulation,[],[f104,f150])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0) ) ),
    inference(superposition,[],[f85,f55])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f77,f64])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f422,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f304,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f304,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f303,f133])).

fof(f133,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f131,f107])).

fof(f107,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f79,f80])).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f63,f64,f64])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f83,f88])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f303,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_subset_1(X1,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f68,f298])).

fof(f298,plain,(
    ! [X8] : k3_subset_1(X8,k1_xboole_0) = X8 ),
    inference(forward_demodulation,[],[f293,f263])).

fof(f263,plain,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f150,f80])).

fof(f293,plain,(
    ! [X8] : k3_subset_1(X8,k1_xboole_0) = k7_subset_1(X8,X8,k1_xboole_0) ),
    inference(resolution,[],[f167,f206])).

fof(f167,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2) ) ),
    inference(backward_demodulation,[],[f132,f150])).

fof(f132,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_subset_1(X1,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f83,f75])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f102,f120])).

fof(f120,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f114,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k5_xboole_0(X0,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f82,f66])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f728,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f727])).

fof(f727,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f169,f726])).

fof(f169,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f153,f150])).

fof(f153,plain,
    ( k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f53,f149])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (27541)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (27563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.52  % (27555)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.53  % (27538)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.53  % (27544)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.54  % (27553)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.54  % (27563)Refutation not found, incomplete strategy% (27563)------------------------------
% 0.23/0.54  % (27563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (27563)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (27563)Memory used [KB]: 10746
% 0.23/0.54  % (27563)Time elapsed: 0.126 s
% 0.23/0.54  % (27563)------------------------------
% 0.23/0.54  % (27563)------------------------------
% 0.23/0.54  % (27537)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (27535)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.54  % (27539)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.55  % (27540)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (27561)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (27543)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.55  % (27550)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (27562)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (27564)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (27564)Refutation not found, incomplete strategy% (27564)------------------------------
% 0.23/0.55  % (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (27564)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (27564)Memory used [KB]: 1663
% 0.23/0.55  % (27564)Time elapsed: 0.001 s
% 0.23/0.55  % (27564)------------------------------
% 0.23/0.55  % (27564)------------------------------
% 0.23/0.56  % (27556)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.56  % (27558)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.56  % (27560)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.56  % (27554)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (27559)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.56  % (27548)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (27542)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (27536)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.57  % (27547)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.57  % (27552)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.58  % (27551)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.58  % (27551)Refutation not found, incomplete strategy% (27551)------------------------------
% 0.23/0.58  % (27551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (27551)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (27551)Memory used [KB]: 10618
% 0.23/0.58  % (27551)Time elapsed: 0.169 s
% 0.23/0.58  % (27551)------------------------------
% 0.23/0.58  % (27551)------------------------------
% 0.23/0.59  % (27557)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.60  % (27546)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.88/0.61  % (27545)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.88/0.61  % (27549)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.19/0.66  % (27545)Refutation not found, incomplete strategy% (27545)------------------------------
% 2.19/0.66  % (27545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (27545)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (27545)Memory used [KB]: 11129
% 2.19/0.67  % (27545)Time elapsed: 0.164 s
% 2.19/0.67  % (27545)------------------------------
% 2.19/0.67  % (27545)------------------------------
% 2.19/0.67  % (27557)Refutation found. Thanks to Tanya!
% 2.19/0.67  % SZS status Theorem for theBenchmark
% 2.19/0.67  % SZS output start Proof for theBenchmark
% 2.19/0.67  fof(f795,plain,(
% 2.19/0.67    $false),
% 2.19/0.67    inference(unit_resulting_resolution,[],[f50,f49,f728,f51,f766,f61])).
% 2.19/0.67  fof(f61,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f29])).
% 2.19/0.67  fof(f29,plain,(
% 2.19/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.67    inference(flattening,[],[f28])).
% 2.19/0.67  fof(f28,plain,(
% 2.19/0.67    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.67    inference(ennf_transformation,[],[f17])).
% 2.19/0.67  fof(f17,axiom,(
% 2.19/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.19/0.67  fof(f766,plain,(
% 2.19/0.67    sK1 = k2_pre_topc(sK0,sK1)),
% 2.19/0.67    inference(subsumption_resolution,[],[f762,f51])).
% 2.19/0.67  fof(f762,plain,(
% 2.19/0.67    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.67    inference(superposition,[],[f746,f283])).
% 2.19/0.67  fof(f283,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.67    inference(subsumption_resolution,[],[f282,f146])).
% 2.19/0.67  fof(f146,plain,(
% 2.19/0.67    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.67    inference(resolution,[],[f70,f50])).
% 2.19/0.67  fof(f70,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f36])).
% 2.19/0.67  fof(f36,plain,(
% 2.19/0.67    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.19/0.67    inference(flattening,[],[f35])).
% 2.19/0.67  fof(f35,plain,(
% 2.19/0.67    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.19/0.67    inference(ennf_transformation,[],[f18])).
% 2.19/0.67  fof(f18,axiom,(
% 2.19/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.19/0.67  fof(f282,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.67    inference(duplicate_literal_removal,[],[f279])).
% 2.19/0.67  fof(f279,plain,(
% 2.19/0.67    ( ! [X1] : (k2_xboole_0(X1,k2_tops_1(sK0,X1)) = k2_pre_topc(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.67    inference(superposition,[],[f243,f78])).
% 2.19/0.67  fof(f78,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f40])).
% 2.19/0.67  fof(f40,plain,(
% 2.19/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.67    inference(flattening,[],[f39])).
% 2.19/0.67  fof(f39,plain,(
% 2.19/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.19/0.67    inference(ennf_transformation,[],[f14])).
% 2.19/0.67  fof(f14,axiom,(
% 2.19/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.19/0.67  fof(f243,plain,(
% 2.19/0.67    ( ! [X0] : (k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.67    inference(resolution,[],[f58,f50])).
% 2.19/0.67  fof(f58,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f26])).
% 2.19/0.67  fof(f26,plain,(
% 2.19/0.67    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.67    inference(ennf_transformation,[],[f21])).
% 2.19/0.67  fof(f21,axiom,(
% 2.19/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.19/0.67  fof(f746,plain,(
% 2.19/0.67    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.19/0.67    inference(superposition,[],[f468,f726])).
% 2.19/0.67  fof(f726,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(global_subsumption,[],[f53,f170,f725])).
% 2.19/0.67  fof(f725,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(subsumption_resolution,[],[f724,f50])).
% 2.19/0.67  fof(f724,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(subsumption_resolution,[],[f720,f51])).
% 2.19/0.67  fof(f720,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(superposition,[],[f59,f237])).
% 2.19/0.67  fof(f237,plain,(
% 2.19/0.67    sK1 = k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(subsumption_resolution,[],[f234,f51])).
% 2.19/0.67  fof(f234,plain,(
% 2.19/0.67    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(resolution,[],[f219,f170])).
% 2.19/0.67  fof(f219,plain,(
% 2.19/0.67    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 2.19/0.67    inference(resolution,[],[f60,f50])).
% 2.19/0.67  fof(f60,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 2.19/0.67    inference(cnf_transformation,[],[f29])).
% 2.19/0.67  fof(f59,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f27])).
% 2.19/0.67  fof(f27,plain,(
% 2.19/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.19/0.67    inference(ennf_transformation,[],[f20])).
% 2.19/0.67  fof(f20,axiom,(
% 2.19/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.19/0.67  fof(f170,plain,(
% 2.19/0.67    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(backward_demodulation,[],[f152,f150])).
% 2.19/0.67  fof(f150,plain,(
% 2.19/0.67    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)) )),
% 2.19/0.67    inference(resolution,[],[f84,f88])).
% 2.19/0.67  fof(f88,plain,(
% 2.19/0.67    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(forward_demodulation,[],[f57,f54])).
% 2.19/0.67  fof(f54,plain,(
% 2.19/0.67    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.19/0.67    inference(cnf_transformation,[],[f10])).
% 2.19/0.67  fof(f10,axiom,(
% 2.19/0.67    ! [X0] : k2_subset_1(X0) = X0),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.19/0.67  fof(f57,plain,(
% 2.19/0.67    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f12])).
% 2.19/0.67  fof(f12,axiom,(
% 2.19/0.67    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.19/0.67  fof(f84,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.19/0.67    inference(definition_unfolding,[],[f76,f64])).
% 2.19/0.67  fof(f64,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f2])).
% 2.19/0.67  fof(f2,axiom,(
% 2.19/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.19/0.67  fof(f76,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f37])).
% 2.19/0.67  fof(f37,plain,(
% 2.19/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.67    inference(ennf_transformation,[],[f15])).
% 2.19/0.67  fof(f15,axiom,(
% 2.19/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.19/0.67  fof(f152,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 2.19/0.67    inference(backward_demodulation,[],[f52,f149])).
% 2.19/0.67  fof(f149,plain,(
% 2.19/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 2.19/0.67    inference(resolution,[],[f84,f51])).
% 2.19/0.67  fof(f52,plain,(
% 2.19/0.67    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(cnf_transformation,[],[f45])).
% 2.19/0.67  fof(f45,plain,(
% 2.19/0.67    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.19/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 2.19/0.67  fof(f43,plain,(
% 2.19/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.19/0.67    introduced(choice_axiom,[])).
% 2.19/0.67  fof(f44,plain,(
% 2.19/0.67    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.19/0.67    introduced(choice_axiom,[])).
% 2.19/0.67  fof(f42,plain,(
% 2.19/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.67    inference(flattening,[],[f41])).
% 2.19/0.67  fof(f41,plain,(
% 2.19/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.67    inference(nnf_transformation,[],[f25])).
% 2.19/0.67  fof(f25,plain,(
% 2.19/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.19/0.67    inference(flattening,[],[f24])).
% 2.19/0.67  fof(f24,plain,(
% 2.19/0.67    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.19/0.67    inference(ennf_transformation,[],[f23])).
% 2.19/0.67  fof(f23,negated_conjecture,(
% 2.19/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.19/0.67    inference(negated_conjecture,[],[f22])).
% 2.19/0.67  fof(f22,conjecture,(
% 2.19/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.19/0.67  fof(f53,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f45])).
% 2.19/0.67  fof(f468,plain,(
% 2.19/0.67    ( ! [X12,X11] : (k2_xboole_0(X11,k7_subset_1(X11,X11,X12)) = X11) )),
% 2.19/0.67    inference(resolution,[],[f448,f155])).
% 2.19/0.67  fof(f155,plain,(
% 2.19/0.67    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 2.19/0.67    inference(backward_demodulation,[],[f81,f150])).
% 2.19/0.67  fof(f81,plain,(
% 2.19/0.67    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f62,f64])).
% 2.19/0.67  fof(f62,plain,(
% 2.19/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f5])).
% 2.19/0.67  fof(f5,axiom,(
% 2.19/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.19/0.67  fof(f448,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X0) = X1) )),
% 2.19/0.67    inference(forward_demodulation,[],[f427,f55])).
% 2.19/0.67  fof(f55,plain,(
% 2.19/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.67    inference(cnf_transformation,[],[f3])).
% 2.19/0.67  fof(f3,axiom,(
% 2.19/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.19/0.67  fof(f427,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 2.19/0.67    inference(backward_demodulation,[],[f124,f423])).
% 2.19/0.67  fof(f423,plain,(
% 2.19/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.67    inference(subsumption_resolution,[],[f422,f206])).
% 2.19/0.67  fof(f206,plain,(
% 2.19/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.19/0.67    inference(resolution,[],[f162,f155])).
% 2.19/0.67  fof(f162,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0) | r1_tarski(X1,X0)) )),
% 2.19/0.67    inference(backward_demodulation,[],[f104,f150])).
% 2.19/0.67  fof(f104,plain,(
% 2.19/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k1_xboole_0)) )),
% 2.19/0.67    inference(superposition,[],[f85,f55])).
% 2.19/0.67  fof(f85,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f77,f64])).
% 2.19/0.67  fof(f77,plain,(
% 2.19/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f38])).
% 2.19/0.67  fof(f38,plain,(
% 2.19/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.19/0.67    inference(ennf_transformation,[],[f8])).
% 2.19/0.67  fof(f8,axiom,(
% 2.19/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.19/0.67  fof(f422,plain,(
% 2.19/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 2.19/0.67    inference(resolution,[],[f304,f75])).
% 2.19/0.67  fof(f75,plain,(
% 2.19/0.67    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f48])).
% 2.19/0.67  fof(f48,plain,(
% 2.19/0.67    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.19/0.67    inference(nnf_transformation,[],[f16])).
% 2.19/0.67  fof(f16,axiom,(
% 2.19/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.19/0.67  fof(f304,plain,(
% 2.19/0.67    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 2.19/0.67    inference(forward_demodulation,[],[f303,f133])).
% 2.19/0.67  fof(f133,plain,(
% 2.19/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,X0)) )),
% 2.19/0.67    inference(forward_demodulation,[],[f131,f107])).
% 2.19/0.67  fof(f107,plain,(
% 2.19/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.19/0.67    inference(superposition,[],[f79,f80])).
% 2.19/0.67  fof(f80,plain,(
% 2.19/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.19/0.67    inference(definition_unfolding,[],[f56,f64])).
% 2.19/0.67  fof(f56,plain,(
% 2.19/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.67    inference(cnf_transformation,[],[f7])).
% 2.19/0.67  fof(f7,axiom,(
% 2.19/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.67  fof(f79,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 2.19/0.67    inference(definition_unfolding,[],[f63,f64,f64])).
% 2.19/0.67  fof(f63,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f9])).
% 2.19/0.67  fof(f9,axiom,(
% 2.19/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.19/0.67  fof(f131,plain,(
% 2.19/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0)) )),
% 2.19/0.67    inference(resolution,[],[f83,f88])).
% 2.19/0.67  fof(f83,plain,(
% 2.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.19/0.67    inference(definition_unfolding,[],[f67,f64])).
% 2.19/0.67  fof(f67,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f31])).
% 2.19/0.67  fof(f31,plain,(
% 2.19/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.67    inference(ennf_transformation,[],[f11])).
% 2.19/0.67  fof(f11,axiom,(
% 2.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.19/0.67  fof(f303,plain,(
% 2.19/0.67    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 2.19/0.67    inference(superposition,[],[f68,f298])).
% 2.19/0.67  fof(f298,plain,(
% 2.19/0.67    ( ! [X8] : (k3_subset_1(X8,k1_xboole_0) = X8) )),
% 2.19/0.67    inference(forward_demodulation,[],[f293,f263])).
% 2.19/0.67  fof(f263,plain,(
% 2.19/0.67    ( ! [X0] : (k7_subset_1(X0,X0,k1_xboole_0) = X0) )),
% 2.19/0.67    inference(superposition,[],[f150,f80])).
% 2.19/0.67  fof(f293,plain,(
% 2.19/0.67    ( ! [X8] : (k3_subset_1(X8,k1_xboole_0) = k7_subset_1(X8,X8,k1_xboole_0)) )),
% 2.19/0.67    inference(resolution,[],[f167,f206])).
% 2.19/0.67  fof(f167,plain,(
% 2.19/0.67    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2)) )),
% 2.19/0.67    inference(backward_demodulation,[],[f132,f150])).
% 2.19/0.67  fof(f132,plain,(
% 2.19/0.67    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_subset_1(X1,X2) | ~r1_tarski(X2,X1)) )),
% 2.19/0.67    inference(resolution,[],[f83,f75])).
% 2.19/0.67  fof(f68,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.67    inference(cnf_transformation,[],[f32])).
% 2.19/0.67  fof(f32,plain,(
% 2.19/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.67    inference(ennf_transformation,[],[f13])).
% 2.19/0.67  fof(f13,axiom,(
% 2.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.19/0.67  fof(f124,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 2.19/0.67    inference(backward_demodulation,[],[f102,f120])).
% 2.19/0.67  fof(f120,plain,(
% 2.19/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) )),
% 2.19/0.67    inference(subsumption_resolution,[],[f114,f86])).
% 2.19/0.67  fof(f86,plain,(
% 2.19/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.19/0.67    inference(equality_resolution,[],[f72])).
% 2.19/0.67  fof(f72,plain,(
% 2.19/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.19/0.67    inference(cnf_transformation,[],[f47])).
% 2.19/0.67  fof(f47,plain,(
% 2.19/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.67    inference(flattening,[],[f46])).
% 2.19/0.67  fof(f46,plain,(
% 2.19/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.67    inference(nnf_transformation,[],[f1])).
% 2.19/0.67  fof(f1,axiom,(
% 2.19/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.67  fof(f114,plain,(
% 2.19/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 2.19/0.67    inference(superposition,[],[f107,f66])).
% 2.19/0.67  fof(f66,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f30])).
% 2.19/0.67  fof(f30,plain,(
% 2.19/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/0.67    inference(ennf_transformation,[],[f4])).
% 2.19/0.67  fof(f4,axiom,(
% 2.19/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.19/0.67  fof(f102,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,X1)) )),
% 2.19/0.67    inference(superposition,[],[f82,f66])).
% 2.19/0.67  fof(f82,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.19/0.67    inference(definition_unfolding,[],[f65,f64])).
% 2.19/0.67  fof(f65,plain,(
% 2.19/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.19/0.67    inference(cnf_transformation,[],[f6])).
% 2.19/0.67  fof(f6,axiom,(
% 2.19/0.67    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.19/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.19/0.67  fof(f51,plain,(
% 2.19/0.67    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.67    inference(cnf_transformation,[],[f45])).
% 2.19/0.67  fof(f728,plain,(
% 2.19/0.67    ~v4_pre_topc(sK1,sK0)),
% 2.19/0.67    inference(trivial_inequality_removal,[],[f727])).
% 2.19/0.67  fof(f727,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.19/0.67    inference(backward_demodulation,[],[f169,f726])).
% 2.19/0.67  fof(f169,plain,(
% 2.19/0.67    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 2.19/0.67    inference(backward_demodulation,[],[f153,f150])).
% 2.19/0.67  fof(f153,plain,(
% 2.19/0.67    k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~v4_pre_topc(sK1,sK0)),
% 2.19/0.67    inference(backward_demodulation,[],[f53,f149])).
% 2.19/0.67  fof(f49,plain,(
% 2.19/0.67    v2_pre_topc(sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f45])).
% 2.19/0.67  fof(f50,plain,(
% 2.19/0.67    l1_pre_topc(sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f45])).
% 2.19/0.67  % SZS output end Proof for theBenchmark
% 2.19/0.67  % (27557)------------------------------
% 2.19/0.67  % (27557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (27557)Termination reason: Refutation
% 2.19/0.67  
% 2.19/0.67  % (27557)Memory used [KB]: 6908
% 2.19/0.67  % (27557)Time elapsed: 0.200 s
% 2.19/0.67  % (27557)------------------------------
% 2.19/0.67  % (27557)------------------------------
% 2.19/0.67  % (27532)Success in time 0.3 s
%------------------------------------------------------------------------------
