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
% DateTime   : Thu Dec  3 13:12:10 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 358 expanded)
%              Number of leaves         :   18 ( 100 expanded)
%              Depth                    :   29
%              Number of atoms          :  303 (1477 expanded)
%              Number of equality atoms :   96 ( 464 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5422,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5421,f108])).

fof(f108,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f107,f102])).

fof(f102,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f47,f97])).

fof(f97,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f94,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f56,f41])).

fof(f41,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f107,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f5421,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f5420,f5009])).

fof(f5009,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f5008,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f5008,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5007,f39])).

fof(f5007,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5006,f40])).

fof(f5006,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f5005])).

fof(f5005,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f53,f4742])).

fof(f4742,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f4741,f39])).

fof(f4741,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f4722,f40])).

fof(f4722,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f4687,f118])).

fof(f118,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f117,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f4687,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f4651,f78])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f74,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f50,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4651,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f50,f4641])).

fof(f4641,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f4640,f2371])).

fof(f2371,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(backward_demodulation,[],[f165,f2368])).

fof(f2368,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f2266,f43])).

fof(f2266,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f1996,f224])).

fof(f224,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f208,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f208,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f80,f43])).

fof(f80,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f55,f49])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1996,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),X5) ),
    inference(backward_demodulation,[],[f170,f1994])).

fof(f1994,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8)) ),
    inference(forward_demodulation,[],[f1993,f55])).

fof(f1993,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8)) ),
    inference(subsumption_resolution,[],[f1893,f47])).

fof(f1893,plain,(
    ! [X6,X8,X7] :
      ( k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8))
      | ~ r1_tarski(k4_xboole_0(X6,X7),X6) ) ),
    inference(superposition,[],[f170,f59])).

fof(f59,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f170,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),X5) ),
    inference(superposition,[],[f55,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f49])).

fof(f165,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f66,f48])).

fof(f4640,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f4639,f39])).

fof(f4639,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f4622,f40])).

fof(f4622,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f490,f435])).

fof(f435,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f49,f130])).

fof(f130,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f45,f56])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f490,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f489,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f47,f49])).

fof(f489,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f469,f48])).

fof(f469,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f257,f43])).

fof(f257,plain,(
    ! [X20] :
      ( k3_xboole_0(k2_tops_1(sK0,sK1),X20) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),X20)))
      | v4_pre_topc(sK1,sK0) ) ),
    inference(superposition,[],[f85,f97])).

fof(f85,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f49,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f5420,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f5418])).

fof(f5418,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f4634,f59])).

fof(f4634,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f4633,f39])).

fof(f4633,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f4618,f40])).

fof(f4618,plain,
    ( k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f98,f435])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f42,f56])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (17887)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (17883)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (17888)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (17892)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (17884)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17889)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (17896)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (17891)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17898)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (17895)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17890)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (17885)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (17894)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (17882)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (17886)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (17899)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (17893)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (17897)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 3.20/0.80  % (17885)Refutation found. Thanks to Tanya!
% 3.20/0.80  % SZS status Theorem for theBenchmark
% 3.20/0.80  % SZS output start Proof for theBenchmark
% 3.20/0.80  fof(f5422,plain,(
% 3.20/0.80    $false),
% 3.20/0.80    inference(subsumption_resolution,[],[f5421,f108])).
% 3.20/0.80  fof(f108,plain,(
% 3.20/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.20/0.80    inference(subsumption_resolution,[],[f107,f102])).
% 3.20/0.80  fof(f102,plain,(
% 3.20/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(superposition,[],[f47,f97])).
% 3.20/0.80  fof(f97,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f94,f40])).
% 3.20/0.80  fof(f40,plain,(
% 3.20/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.80    inference(cnf_transformation,[],[f37])).
% 3.20/0.80  fof(f37,plain,(
% 3.20/0.80    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.20/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 3.20/0.80  fof(f35,plain,(
% 3.20/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.20/0.80    introduced(choice_axiom,[])).
% 3.20/0.80  fof(f36,plain,(
% 3.20/0.80    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.20/0.80    introduced(choice_axiom,[])).
% 3.20/0.80  fof(f34,plain,(
% 3.20/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.80    inference(flattening,[],[f33])).
% 3.20/0.80  fof(f33,plain,(
% 3.20/0.80    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.80    inference(nnf_transformation,[],[f19])).
% 3.20/0.80  fof(f19,plain,(
% 3.20/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.80    inference(flattening,[],[f18])).
% 3.20/0.80  fof(f18,plain,(
% 3.20/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.20/0.80    inference(ennf_transformation,[],[f17])).
% 3.20/0.80  fof(f17,negated_conjecture,(
% 3.20/0.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.20/0.80    inference(negated_conjecture,[],[f16])).
% 3.20/0.80  fof(f16,conjecture,(
% 3.20/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.20/0.80  fof(f94,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(superposition,[],[f56,f41])).
% 3.20/0.80  fof(f41,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(cnf_transformation,[],[f37])).
% 3.20/0.80  fof(f56,plain,(
% 3.20/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/0.80    inference(cnf_transformation,[],[f30])).
% 3.20/0.80  fof(f30,plain,(
% 3.20/0.80    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.80    inference(ennf_transformation,[],[f10])).
% 3.20/0.80  fof(f10,axiom,(
% 3.20/0.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.20/0.80  fof(f47,plain,(
% 3.20/0.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f5])).
% 3.20/0.80  fof(f5,axiom,(
% 3.20/0.80    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.20/0.80  fof(f107,plain,(
% 3.20/0.80    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.20/0.80    inference(subsumption_resolution,[],[f104,f39])).
% 3.20/0.80  fof(f39,plain,(
% 3.20/0.80    l1_pre_topc(sK0)),
% 3.20/0.80    inference(cnf_transformation,[],[f37])).
% 3.20/0.80  fof(f104,plain,(
% 3.20/0.80    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(resolution,[],[f46,f40])).
% 3.20/0.80  fof(f46,plain,(
% 3.20/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f23])).
% 3.20/0.80  fof(f23,plain,(
% 3.20/0.80    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.80    inference(flattening,[],[f22])).
% 3.20/0.80  fof(f22,plain,(
% 3.20/0.80    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.80    inference(ennf_transformation,[],[f14])).
% 3.20/0.80  fof(f14,axiom,(
% 3.20/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.20/0.80  fof(f5421,plain,(
% 3.20/0.80    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.20/0.80    inference(subsumption_resolution,[],[f5420,f5009])).
% 3.20/0.80  fof(f5009,plain,(
% 3.20/0.80    v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f5008,f38])).
% 3.20/0.80  fof(f38,plain,(
% 3.20/0.80    v2_pre_topc(sK0)),
% 3.20/0.80    inference(cnf_transformation,[],[f37])).
% 3.20/0.80  fof(f5008,plain,(
% 3.20/0.80    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f5007,f39])).
% 3.20/0.80  fof(f5007,plain,(
% 3.20/0.80    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f5006,f40])).
% 3.20/0.80  fof(f5006,plain,(
% 3.20/0.80    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.20/0.80    inference(duplicate_literal_removal,[],[f5005])).
% 3.20/0.80  fof(f5005,plain,(
% 3.20/0.80    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(superposition,[],[f53,f4742])).
% 3.20/0.80  fof(f4742,plain,(
% 3.20/0.80    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4741,f39])).
% 3.20/0.80  fof(f4741,plain,(
% 3.20/0.80    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4722,f40])).
% 3.20/0.80  fof(f4722,plain,(
% 3.20/0.80    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(superposition,[],[f4687,f118])).
% 3.20/0.80  fof(f118,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.20/0.80    inference(subsumption_resolution,[],[f117,f54])).
% 3.20/0.80  fof(f54,plain,(
% 3.20/0.80    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f29])).
% 3.20/0.80  fof(f29,plain,(
% 3.20/0.80    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.20/0.80    inference(flattening,[],[f28])).
% 3.20/0.80  fof(f28,plain,(
% 3.20/0.80    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.20/0.80    inference(ennf_transformation,[],[f11])).
% 3.20/0.80  fof(f11,axiom,(
% 3.20/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.20/0.80  fof(f117,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.20/0.80    inference(duplicate_literal_removal,[],[f114])).
% 3.20/0.80  fof(f114,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.20/0.80    inference(superposition,[],[f44,f57])).
% 3.20/0.80  fof(f57,plain,(
% 3.20/0.80    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/0.80    inference(cnf_transformation,[],[f32])).
% 3.20/0.80  fof(f32,plain,(
% 3.20/0.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.80    inference(flattening,[],[f31])).
% 3.20/0.80  fof(f31,plain,(
% 3.20/0.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.20/0.80    inference(ennf_transformation,[],[f9])).
% 3.20/0.80  fof(f9,axiom,(
% 3.20/0.80    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.20/0.80  fof(f44,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f20])).
% 3.20/0.80  fof(f20,plain,(
% 3.20/0.80    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.80    inference(ennf_transformation,[],[f13])).
% 3.20/0.80  fof(f13,axiom,(
% 3.20/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.20/0.80  fof(f4687,plain,(
% 3.20/0.80    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(forward_demodulation,[],[f4651,f78])).
% 3.20/0.80  fof(f78,plain,(
% 3.20/0.80    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.80    inference(forward_demodulation,[],[f74,f43])).
% 3.20/0.80  fof(f43,plain,(
% 3.20/0.80    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.80    inference(cnf_transformation,[],[f3])).
% 3.20/0.80  fof(f3,axiom,(
% 3.20/0.80    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.20/0.80  fof(f74,plain,(
% 3.20/0.80    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 3.20/0.80    inference(superposition,[],[f50,f65])).
% 3.20/0.80  fof(f65,plain,(
% 3.20/0.80    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.20/0.80    inference(resolution,[],[f63,f47])).
% 3.20/0.80  fof(f63,plain,(
% 3.20/0.80    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.20/0.80    inference(superposition,[],[f52,f43])).
% 3.20/0.80  fof(f52,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f25])).
% 3.20/0.80  fof(f25,plain,(
% 3.20/0.80    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.20/0.80    inference(ennf_transformation,[],[f2])).
% 3.20/0.80  fof(f2,axiom,(
% 3.20/0.80    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.20/0.80  fof(f50,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.20/0.80    inference(cnf_transformation,[],[f8])).
% 3.20/0.80  fof(f8,axiom,(
% 3.20/0.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.20/0.80  fof(f4651,plain,(
% 3.20/0.80    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(superposition,[],[f50,f4641])).
% 3.20/0.80  fof(f4641,plain,(
% 3.20/0.80    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(forward_demodulation,[],[f4640,f2371])).
% 3.20/0.80  fof(f2371,plain,(
% 3.20/0.80    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 3.20/0.80    inference(backward_demodulation,[],[f165,f2368])).
% 3.20/0.80  fof(f2368,plain,(
% 3.20/0.80    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 3.20/0.80    inference(forward_demodulation,[],[f2266,f43])).
% 3.20/0.80  fof(f2266,plain,(
% 3.20/0.80    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 3.20/0.80    inference(superposition,[],[f1996,f224])).
% 3.20/0.80  fof(f224,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 3.20/0.80    inference(forward_demodulation,[],[f208,f49])).
% 3.20/0.80  fof(f49,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.20/0.80    inference(cnf_transformation,[],[f7])).
% 3.20/0.80  fof(f7,axiom,(
% 3.20/0.80    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.20/0.80  fof(f208,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 3.20/0.80    inference(superposition,[],[f80,f43])).
% 3.20/0.80  fof(f80,plain,(
% 3.20/0.80    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.20/0.80    inference(superposition,[],[f55,f49])).
% 3.20/0.80  fof(f55,plain,(
% 3.20/0.80    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.20/0.80    inference(cnf_transformation,[],[f6])).
% 3.20/0.80  fof(f6,axiom,(
% 3.20/0.80    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.20/0.80  fof(f1996,plain,(
% 3.20/0.80    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X5)) = k4_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) )),
% 3.20/0.80    inference(backward_demodulation,[],[f170,f1994])).
% 3.20/0.80  fof(f1994,plain,(
% 3.20/0.80    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,X8)) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8))) )),
% 3.20/0.80    inference(forward_demodulation,[],[f1993,f55])).
% 3.20/0.80  fof(f1993,plain,(
% 3.20/0.80    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8))) )),
% 3.20/0.80    inference(subsumption_resolution,[],[f1893,f47])).
% 3.20/0.80  fof(f1893,plain,(
% 3.20/0.80    ( ! [X6,X8,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8)) | ~r1_tarski(k4_xboole_0(X6,X7),X6)) )),
% 3.20/0.80    inference(superposition,[],[f170,f59])).
% 3.20/0.80  fof(f59,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 3.20/0.80    inference(superposition,[],[f51,f48])).
% 3.20/0.80  fof(f48,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f1])).
% 3.20/0.80  fof(f1,axiom,(
% 3.20/0.80    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.20/0.80  fof(f51,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f24])).
% 3.20/0.80  fof(f24,plain,(
% 3.20/0.80    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.20/0.80    inference(ennf_transformation,[],[f4])).
% 3.20/0.80  fof(f4,axiom,(
% 3.20/0.80    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.20/0.80  fof(f170,plain,(
% 3.20/0.80    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,k4_xboole_0(X3,X4)),X5)) )),
% 3.20/0.80    inference(superposition,[],[f55,f66])).
% 3.20/0.80  fof(f66,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.20/0.80    inference(superposition,[],[f49,f49])).
% 3.20/0.80  fof(f165,plain,(
% 3.20/0.80    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X5,X4))) )),
% 3.20/0.80    inference(superposition,[],[f66,f48])).
% 3.20/0.80  fof(f4640,plain,(
% 3.20/0.80    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4639,f39])).
% 3.20/0.80  fof(f4639,plain,(
% 3.20/0.80    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4622,f40])).
% 3.20/0.80  fof(f4622,plain,(
% 3.20/0.80    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(superposition,[],[f490,f435])).
% 3.20/0.80  fof(f435,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k3_xboole_0(X2,k2_tops_1(X3,X2)) = k4_xboole_0(X2,k1_tops_1(X3,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 3.20/0.80    inference(superposition,[],[f49,f130])).
% 3.20/0.80  fof(f130,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.20/0.80    inference(duplicate_literal_removal,[],[f127])).
% 3.20/0.80  fof(f127,plain,(
% 3.20/0.80    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.20/0.80    inference(superposition,[],[f45,f56])).
% 3.20/0.80  fof(f45,plain,(
% 3.20/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f21])).
% 3.20/0.80  fof(f21,plain,(
% 3.20/0.80    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.80    inference(ennf_transformation,[],[f15])).
% 3.20/0.80  fof(f15,axiom,(
% 3.20/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.20/0.80  fof(f490,plain,(
% 3.20/0.80    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(forward_demodulation,[],[f489,f68])).
% 3.20/0.80  fof(f68,plain,(
% 3.20/0.80    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 3.20/0.80    inference(resolution,[],[f67,f63])).
% 3.20/0.80  fof(f67,plain,(
% 3.20/0.80    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.20/0.80    inference(superposition,[],[f47,f49])).
% 3.20/0.80  fof(f489,plain,(
% 3.20/0.80    k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(forward_demodulation,[],[f469,f48])).
% 3.20/0.80  fof(f469,plain,(
% 3.20/0.80    k3_xboole_0(k2_tops_1(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(superposition,[],[f257,f43])).
% 3.20/0.80  fof(f257,plain,(
% 3.20/0.80    ( ! [X20] : (k3_xboole_0(k2_tops_1(sK0,sK1),X20) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),X20))) | v4_pre_topc(sK1,sK0)) )),
% 3.20/0.80    inference(superposition,[],[f85,f97])).
% 3.20/0.80  fof(f85,plain,(
% 3.20/0.80    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 3.20/0.80    inference(superposition,[],[f49,f55])).
% 3.20/0.80  fof(f53,plain,(
% 3.20/0.80    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.20/0.80    inference(cnf_transformation,[],[f27])).
% 3.20/0.80  fof(f27,plain,(
% 3.20/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.20/0.80    inference(flattening,[],[f26])).
% 3.20/0.80  fof(f26,plain,(
% 3.20/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.20/0.80    inference(ennf_transformation,[],[f12])).
% 3.20/0.80  fof(f12,axiom,(
% 3.20/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.20/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.20/0.80  fof(f5420,plain,(
% 3.20/0.80    ~v4_pre_topc(sK1,sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.20/0.80    inference(trivial_inequality_removal,[],[f5418])).
% 3.20/0.80  fof(f5418,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.20/0.80    inference(superposition,[],[f4634,f59])).
% 3.20/0.80  fof(f4634,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4633,f39])).
% 3.20/0.80  fof(f4633,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f4618,f40])).
% 3.20/0.80  fof(f4618,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.20/0.80    inference(superposition,[],[f98,f435])).
% 3.20/0.80  fof(f98,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(subsumption_resolution,[],[f95,f40])).
% 3.20/0.80  fof(f95,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.80    inference(superposition,[],[f42,f56])).
% 3.20/0.80  fof(f42,plain,(
% 3.20/0.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.20/0.80    inference(cnf_transformation,[],[f37])).
% 3.20/0.80  % SZS output end Proof for theBenchmark
% 3.20/0.80  % (17885)------------------------------
% 3.20/0.80  % (17885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.80  % (17885)Termination reason: Refutation
% 3.20/0.80  
% 3.20/0.80  % (17885)Memory used [KB]: 5884
% 3.20/0.80  % (17885)Time elapsed: 0.381 s
% 3.20/0.80  % (17885)------------------------------
% 3.20/0.80  % (17885)------------------------------
% 3.20/0.80  % (17880)Success in time 0.444 s
%------------------------------------------------------------------------------
