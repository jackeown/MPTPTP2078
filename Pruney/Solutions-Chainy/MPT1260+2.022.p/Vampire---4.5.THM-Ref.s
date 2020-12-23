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
% DateTime   : Thu Dec  3 13:11:36 EST 2020

% Result     : Theorem 6.18s
% Output     : Refutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 522 expanded)
%              Number of leaves         :   20 ( 141 expanded)
%              Depth                    :   36
%              Number of atoms          :  317 (2498 expanded)
%              Number of equality atoms :   87 ( 709 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8643,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8642,f2435])).

fof(f2435,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2434,f62])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f2434,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2433,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f2433,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2430,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f2430,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f2429])).

fof(f2429,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f85,f2362])).

fof(f2362,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2361,f63])).

fof(f2361,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2340,f64])).

fof(f2340,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f2330,f262])).

fof(f262,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f71,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f2330,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2317,f122])).

fof(f122,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f119,f68])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f79,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2317,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f79,f2262])).

fof(f2262,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2261,f63])).

fof(f2261,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2259,f64])).

fof(f2259,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f2250,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2250,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2249,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f110,f67])).

fof(f110,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f78,f68])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2249,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2231,f293])).

fof(f293,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f104,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f77,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2231,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f78,f2119])).

fof(f2119,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f2084,f245])).

fof(f245,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f244,f63])).

fof(f244,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f242,f64])).

fof(f242,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f238,f86])).

fof(f238,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f75,f221])).

fof(f221,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f95,f65])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2084,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f616,f74])).

fof(f74,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f616,plain,(
    ! [X35] :
      ( k4_xboole_0(X35,sK1) = k3_xboole_0(X35,k2_tops_1(sK0,sK1))
      | ~ r1_tarski(X35,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(superposition,[],[f157,f221])).

fof(f157,plain,(
    ! [X6,X4,X5] :
      ( k3_xboole_0(X4,k4_xboole_0(X5,X6)) = k4_xboole_0(X4,X6)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f92,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f92,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f8642,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f8641])).

fof(f8641,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f66,f8640])).

fof(f8640,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f8639,f63])).

fof(f8639,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f8620,f64])).

fof(f8620,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f72,f8282])).

fof(f8282,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f8275,f2435])).

fof(f8275,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f8274,f296])).

fof(f296,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f290,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f290,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f288,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f288,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f281,f64])).

fof(f281,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X18,sK0)
      | r1_tarski(X18,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X18,sK1) ) ),
    inference(subsumption_resolution,[],[f278,f63])).

fof(f278,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,sK1)
      | ~ v3_pre_topc(X18,sK0)
      | r1_tarski(X18,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f73,f64])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f8274,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f8270,f63])).

fof(f8270,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1503,f64])).

fof(f1503,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f75,f262])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:56:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.51  % (32284)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (32276)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (32292)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (32268)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (32291)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (32284)Refutation not found, incomplete strategy% (32284)------------------------------
% 0.20/0.52  % (32284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32283)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (32270)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (32284)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32284)Memory used [KB]: 10746
% 0.20/0.53  % (32284)Time elapsed: 0.106 s
% 0.20/0.53  % (32284)------------------------------
% 0.20/0.53  % (32284)------------------------------
% 0.20/0.53  % (32271)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (32273)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (32272)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (32274)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (32275)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (32269)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (32287)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (32297)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (32296)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (32295)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (32285)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (32289)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (32282)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (32288)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (32293)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (32279)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (32277)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (32290)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (32281)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (32280)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.57  % (32294)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.57  % (32296)Refutation not found, incomplete strategy% (32296)------------------------------
% 1.56/0.57  % (32296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (32296)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (32296)Memory used [KB]: 10874
% 1.56/0.58  % (32296)Time elapsed: 0.170 s
% 1.56/0.58  % (32296)------------------------------
% 1.56/0.58  % (32296)------------------------------
% 1.74/0.59  % (32286)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.74/0.62  % (32278)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.16/0.65  % (32278)Refutation not found, incomplete strategy% (32278)------------------------------
% 2.16/0.65  % (32278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (32278)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.65  
% 2.16/0.65  % (32278)Memory used [KB]: 10874
% 2.16/0.65  % (32278)Time elapsed: 0.193 s
% 2.16/0.65  % (32278)------------------------------
% 2.16/0.65  % (32278)------------------------------
% 2.27/0.68  % (32301)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.73/0.72  % (32307)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.06/0.78  % (32332)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.06/0.82  % (32292)Time limit reached!
% 3.06/0.82  % (32292)------------------------------
% 3.06/0.82  % (32292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.82  % (32292)Termination reason: Time limit
% 3.06/0.82  
% 3.06/0.82  % (32292)Memory used [KB]: 14583
% 3.06/0.82  % (32292)Time elapsed: 0.417 s
% 3.06/0.82  % (32292)------------------------------
% 3.06/0.82  % (32292)------------------------------
% 3.06/0.83  % (32270)Time limit reached!
% 3.06/0.83  % (32270)------------------------------
% 3.06/0.83  % (32270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.83  % (32270)Termination reason: Time limit
% 3.06/0.83  
% 3.06/0.83  % (32270)Memory used [KB]: 6652
% 3.06/0.83  % (32270)Time elapsed: 0.417 s
% 3.06/0.83  % (32270)------------------------------
% 3.06/0.83  % (32270)------------------------------
% 3.91/0.91  % (32297)Time limit reached!
% 3.91/0.91  % (32297)------------------------------
% 3.91/0.91  % (32297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (32274)Time limit reached!
% 3.91/0.91  % (32274)------------------------------
% 3.91/0.91  % (32274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.91  % (32274)Termination reason: Time limit
% 3.91/0.91  
% 3.91/0.91  % (32274)Memory used [KB]: 14583
% 3.91/0.91  % (32274)Time elapsed: 0.504 s
% 3.91/0.91  % (32274)------------------------------
% 3.91/0.91  % (32274)------------------------------
% 3.91/0.92  % (32297)Termination reason: Time limit
% 3.91/0.92  % (32297)Termination phase: Saturation
% 3.91/0.92  
% 3.91/0.92  % (32297)Memory used [KB]: 7419
% 3.91/0.92  % (32297)Time elapsed: 0.500 s
% 3.91/0.92  % (32297)------------------------------
% 3.91/0.92  % (32297)------------------------------
% 3.91/0.93  % (32282)Time limit reached!
% 3.91/0.93  % (32282)------------------------------
% 3.91/0.93  % (32282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.93  % (32282)Termination reason: Time limit
% 3.91/0.93  
% 3.91/0.93  % (32282)Memory used [KB]: 6012
% 3.91/0.93  % (32282)Time elapsed: 0.523 s
% 3.91/0.93  % (32282)------------------------------
% 3.91/0.93  % (32282)------------------------------
% 4.41/0.95  % (32336)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.41/0.96  % (32337)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.41/1.01  % (32338)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.79/1.04  % (32339)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.79/1.05  % (32275)Time limit reached!
% 4.79/1.05  % (32275)------------------------------
% 4.79/1.05  % (32275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.06  % (32275)Termination reason: Time limit
% 4.79/1.06  % (32275)Termination phase: Saturation
% 4.79/1.06  
% 4.79/1.06  % (32275)Memory used [KB]: 8315
% 4.79/1.06  % (32275)Time elapsed: 0.600 s
% 4.79/1.06  % (32275)------------------------------
% 4.79/1.06  % (32275)------------------------------
% 4.79/1.07  % (32340)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.18/1.15  % (32277)Refutation found. Thanks to Tanya!
% 6.18/1.15  % SZS status Theorem for theBenchmark
% 6.18/1.15  % SZS output start Proof for theBenchmark
% 6.18/1.15  fof(f8643,plain,(
% 6.18/1.15    $false),
% 6.18/1.15    inference(subsumption_resolution,[],[f8642,f2435])).
% 6.18/1.15  fof(f2435,plain,(
% 6.18/1.15    v3_pre_topc(sK1,sK0)),
% 6.18/1.15    inference(subsumption_resolution,[],[f2434,f62])).
% 6.18/1.15  fof(f62,plain,(
% 6.18/1.15    v2_pre_topc(sK0)),
% 6.18/1.15    inference(cnf_transformation,[],[f58])).
% 6.18/1.15  fof(f58,plain,(
% 6.18/1.15    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.18/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 6.18/1.15  fof(f56,plain,(
% 6.18/1.15    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.18/1.15    introduced(choice_axiom,[])).
% 6.18/1.15  fof(f57,plain,(
% 6.18/1.15    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.18/1.15    introduced(choice_axiom,[])).
% 6.18/1.15  fof(f55,plain,(
% 6.18/1.15    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.18/1.15    inference(flattening,[],[f54])).
% 6.18/1.15  fof(f54,plain,(
% 6.18/1.15    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.18/1.15    inference(nnf_transformation,[],[f33])).
% 6.18/1.15  fof(f33,plain,(
% 6.18/1.15    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.18/1.15    inference(flattening,[],[f32])).
% 6.18/1.15  fof(f32,plain,(
% 6.18/1.15    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.18/1.15    inference(ennf_transformation,[],[f30])).
% 6.18/1.15  fof(f30,negated_conjecture,(
% 6.18/1.15    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 6.18/1.15    inference(negated_conjecture,[],[f29])).
% 6.18/1.17  fof(f29,conjecture,(
% 6.18/1.17    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 6.18/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 6.18/1.18  fof(f2434,plain,(
% 6.18/1.18    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2433,f63])).
% 6.18/1.18  fof(f63,plain,(
% 6.18/1.18    l1_pre_topc(sK0)),
% 6.18/1.18    inference(cnf_transformation,[],[f58])).
% 6.18/1.18  fof(f2433,plain,(
% 6.18/1.18    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2430,f64])).
% 6.18/1.18  fof(f64,plain,(
% 6.18/1.18    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.18/1.18    inference(cnf_transformation,[],[f58])).
% 6.18/1.18  fof(f2430,plain,(
% 6.18/1.18    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 6.18/1.18    inference(duplicate_literal_removal,[],[f2429])).
% 6.18/1.18  fof(f2429,plain,(
% 6.18/1.18    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f85,f2362])).
% 6.18/1.18  fof(f2362,plain,(
% 6.18/1.18    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2361,f63])).
% 6.18/1.18  fof(f2361,plain,(
% 6.18/1.18    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2340,f64])).
% 6.18/1.18  fof(f2340,plain,(
% 6.18/1.18    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(superposition,[],[f2330,f262])).
% 6.18/1.18  fof(f262,plain,(
% 6.18/1.18    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 6.18/1.18    inference(duplicate_literal_removal,[],[f257])).
% 6.18/1.18  fof(f257,plain,(
% 6.18/1.18    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 6.18/1.18    inference(superposition,[],[f71,f95])).
% 6.18/1.18  fof(f95,plain,(
% 6.18/1.18    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.18/1.18    inference(cnf_transformation,[],[f49])).
% 6.18/1.18  fof(f49,plain,(
% 6.18/1.18    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.18/1.18    inference(ennf_transformation,[],[f19])).
% 6.18/1.18  fof(f19,axiom,(
% 6.18/1.18    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.18/1.18  fof(f71,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f36])).
% 6.18/1.18  fof(f36,plain,(
% 6.18/1.18    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.18/1.18    inference(ennf_transformation,[],[f28])).
% 6.18/1.18  fof(f28,axiom,(
% 6.18/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 6.18/1.18  fof(f2330,plain,(
% 6.18/1.18    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(forward_demodulation,[],[f2317,f122])).
% 6.18/1.18  fof(f122,plain,(
% 6.18/1.18    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.18/1.18    inference(forward_demodulation,[],[f119,f68])).
% 6.18/1.18  fof(f68,plain,(
% 6.18/1.18    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.18/1.18    inference(cnf_transformation,[],[f7])).
% 6.18/1.18  fof(f7,axiom,(
% 6.18/1.18    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 6.18/1.18  fof(f119,plain,(
% 6.18/1.18    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 6.18/1.18    inference(superposition,[],[f79,f67])).
% 6.18/1.18  fof(f67,plain,(
% 6.18/1.18    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f5])).
% 6.18/1.18  fof(f5,axiom,(
% 6.18/1.18    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 6.18/1.18  fof(f79,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.18/1.18    inference(cnf_transformation,[],[f3])).
% 6.18/1.18  fof(f3,axiom,(
% 6.18/1.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.18/1.18  fof(f2317,plain,(
% 6.18/1.18    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f79,f2262])).
% 6.18/1.18  fof(f2262,plain,(
% 6.18/1.18    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2261,f63])).
% 6.18/1.18  fof(f2261,plain,(
% 6.18/1.18    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2259,f64])).
% 6.18/1.18  fof(f2259,plain,(
% 6.18/1.18    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(resolution,[],[f2250,f86])).
% 6.18/1.18  fof(f86,plain,(
% 6.18/1.18    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f47])).
% 6.18/1.18  fof(f47,plain,(
% 6.18/1.18    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.18/1.18    inference(flattening,[],[f46])).
% 6.18/1.18  fof(f46,plain,(
% 6.18/1.18    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.18/1.18    inference(ennf_transformation,[],[f22])).
% 6.18/1.18  fof(f22,axiom,(
% 6.18/1.18    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 6.18/1.18  fof(f2250,plain,(
% 6.18/1.18    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(forward_demodulation,[],[f2249,f113])).
% 6.18/1.18  fof(f113,plain,(
% 6.18/1.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 6.18/1.18    inference(forward_demodulation,[],[f110,f67])).
% 6.18/1.18  fof(f110,plain,(
% 6.18/1.18    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 6.18/1.18    inference(superposition,[],[f78,f68])).
% 6.18/1.18  fof(f78,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.18/1.18    inference(cnf_transformation,[],[f10])).
% 6.18/1.18  fof(f10,axiom,(
% 6.18/1.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.18/1.18  fof(f2249,plain,(
% 6.18/1.18    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(forward_demodulation,[],[f2231,f293])).
% 6.18/1.18  fof(f293,plain,(
% 6.18/1.18    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 6.18/1.18    inference(superposition,[],[f104,f77])).
% 6.18/1.18  fof(f77,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.18/1.18    inference(cnf_transformation,[],[f20])).
% 6.18/1.18  fof(f20,axiom,(
% 6.18/1.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.18/1.18  fof(f104,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 6.18/1.18    inference(superposition,[],[f77,f76])).
% 6.18/1.18  fof(f76,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f12])).
% 6.18/1.18  fof(f12,axiom,(
% 6.18/1.18    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.18/1.18  fof(f2231,plain,(
% 6.18/1.18    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f78,f2119])).
% 6.18/1.18  fof(f2119,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f2084,f245])).
% 6.18/1.18  fof(f245,plain,(
% 6.18/1.18    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f244,f63])).
% 6.18/1.18  fof(f244,plain,(
% 6.18/1.18    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f242,f64])).
% 6.18/1.18  fof(f242,plain,(
% 6.18/1.18    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(resolution,[],[f238,f86])).
% 6.18/1.18  fof(f238,plain,(
% 6.18/1.18    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f75,f221])).
% 6.18/1.18  fof(f221,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f95,f65])).
% 6.18/1.18  fof(f65,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(cnf_transformation,[],[f58])).
% 6.18/1.18  fof(f75,plain,(
% 6.18/1.18    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f6])).
% 6.18/1.18  fof(f6,axiom,(
% 6.18/1.18    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.18/1.18  fof(f2084,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(superposition,[],[f616,f74])).
% 6.18/1.18  fof(f74,plain,(
% 6.18/1.18    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.18/1.18    inference(cnf_transformation,[],[f31])).
% 6.18/1.18  fof(f31,plain,(
% 6.18/1.18    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.18/1.18    inference(rectify,[],[f1])).
% 6.18/1.18  fof(f1,axiom,(
% 6.18/1.18    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.18/1.18  fof(f616,plain,(
% 6.18/1.18    ( ! [X35] : (k4_xboole_0(X35,sK1) = k3_xboole_0(X35,k2_tops_1(sK0,sK1)) | ~r1_tarski(X35,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 6.18/1.18    inference(superposition,[],[f157,f221])).
% 6.18/1.18  fof(f157,plain,(
% 6.18/1.18    ( ! [X6,X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X5,X6)) = k4_xboole_0(X4,X6) | ~r1_tarski(X4,X5)) )),
% 6.18/1.18    inference(superposition,[],[f92,f81])).
% 6.18/1.18  fof(f81,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f40])).
% 6.18/1.18  fof(f40,plain,(
% 6.18/1.18    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.18/1.18    inference(ennf_transformation,[],[f4])).
% 6.18/1.18  fof(f4,axiom,(
% 6.18/1.18    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.18/1.18  fof(f92,plain,(
% 6.18/1.18    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f11])).
% 6.18/1.18  fof(f11,axiom,(
% 6.18/1.18    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 6.18/1.18  fof(f85,plain,(
% 6.18/1.18    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f45])).
% 6.18/1.18  fof(f45,plain,(
% 6.18/1.18    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.18/1.18    inference(flattening,[],[f44])).
% 6.18/1.18  fof(f44,plain,(
% 6.18/1.18    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.18/1.18    inference(ennf_transformation,[],[f23])).
% 6.18/1.18  fof(f23,axiom,(
% 6.18/1.18    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 6.18/1.18  fof(f8642,plain,(
% 6.18/1.18    ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(trivial_inequality_removal,[],[f8641])).
% 6.18/1.18  fof(f8641,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(backward_demodulation,[],[f66,f8640])).
% 6.18/1.18  fof(f8640,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 6.18/1.18    inference(subsumption_resolution,[],[f8639,f63])).
% 6.18/1.18  fof(f8639,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f8620,f64])).
% 6.18/1.18  fof(f8620,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(superposition,[],[f72,f8282])).
% 6.18/1.18  fof(f8282,plain,(
% 6.18/1.18    sK1 = k1_tops_1(sK0,sK1)),
% 6.18/1.18    inference(subsumption_resolution,[],[f8275,f2435])).
% 6.18/1.18  fof(f8275,plain,(
% 6.18/1.18    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(resolution,[],[f8274,f296])).
% 6.18/1.18  fof(f296,plain,(
% 6.18/1.18    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(resolution,[],[f290,f89])).
% 6.18/1.18  fof(f89,plain,(
% 6.18/1.18    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f60])).
% 6.18/1.18  fof(f60,plain,(
% 6.18/1.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.18/1.18    inference(flattening,[],[f59])).
% 6.18/1.18  fof(f59,plain,(
% 6.18/1.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.18/1.18    inference(nnf_transformation,[],[f2])).
% 6.18/1.18  fof(f2,axiom,(
% 6.18/1.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.18/1.18  fof(f290,plain,(
% 6.18/1.18    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(subsumption_resolution,[],[f288,f98])).
% 6.18/1.18  fof(f98,plain,(
% 6.18/1.18    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.18/1.18    inference(equality_resolution,[],[f88])).
% 6.18/1.18  fof(f88,plain,(
% 6.18/1.18    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.18/1.18    inference(cnf_transformation,[],[f60])).
% 6.18/1.18  fof(f288,plain,(
% 6.18/1.18    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 6.18/1.18    inference(resolution,[],[f281,f64])).
% 6.18/1.18  fof(f281,plain,(
% 6.18/1.18    ( ! [X18] : (~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~r1_tarski(X18,sK1)) )),
% 6.18/1.18    inference(subsumption_resolution,[],[f278,f63])).
% 6.18/1.18  fof(f278,plain,(
% 6.18/1.18    ( ! [X18] : (~r1_tarski(X18,sK1) | ~v3_pre_topc(X18,sK0) | r1_tarski(X18,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 6.18/1.18    inference(resolution,[],[f73,f64])).
% 6.18/1.18  fof(f73,plain,(
% 6.18/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f39])).
% 6.18/1.18  fof(f39,plain,(
% 6.18/1.18    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.18/1.18    inference(flattening,[],[f38])).
% 6.18/1.18  fof(f38,plain,(
% 6.18/1.18    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.18/1.18    inference(ennf_transformation,[],[f25])).
% 6.18/1.18  fof(f25,axiom,(
% 6.18/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 6.18/1.18  fof(f8274,plain,(
% 6.18/1.18    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 6.18/1.18    inference(subsumption_resolution,[],[f8270,f63])).
% 6.18/1.18  fof(f8270,plain,(
% 6.18/1.18    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 6.18/1.18    inference(resolution,[],[f1503,f64])).
% 6.18/1.18  fof(f1503,plain,(
% 6.18/1.18    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0) | ~l1_pre_topc(X1)) )),
% 6.18/1.18    inference(superposition,[],[f75,f262])).
% 6.18/1.18  fof(f72,plain,(
% 6.18/1.18    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.18/1.18    inference(cnf_transformation,[],[f37])).
% 6.18/1.18  fof(f37,plain,(
% 6.18/1.18    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.18/1.18    inference(ennf_transformation,[],[f24])).
% 6.18/1.18  fof(f24,axiom,(
% 6.18/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 6.18/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 6.18/1.18  fof(f66,plain,(
% 6.18/1.18    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 6.18/1.18    inference(cnf_transformation,[],[f58])).
% 6.18/1.18  % SZS output end Proof for theBenchmark
% 6.18/1.18  % (32277)------------------------------
% 6.18/1.18  % (32277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.18/1.18  % (32277)Termination reason: Refutation
% 6.18/1.18  
% 6.18/1.18  % (32277)Memory used [KB]: 6908
% 6.18/1.18  % (32277)Time elapsed: 0.757 s
% 6.18/1.18  % (32277)------------------------------
% 6.18/1.18  % (32277)------------------------------
% 6.18/1.18  % (32341)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.18/1.18  % (32267)Success in time 0.82 s
%------------------------------------------------------------------------------
