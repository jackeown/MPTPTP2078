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
% DateTime   : Thu Dec  3 13:12:00 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 366 expanded)
%              Number of leaves         :   19 ( 102 expanded)
%              Depth                    :   24
%              Number of atoms          :  260 (1599 expanded)
%              Number of equality atoms :  105 ( 514 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f546,plain,(
    $false ),
    inference(subsumption_resolution,[],[f545,f133])).

fof(f133,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f40,f131])).

fof(f131,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f130,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f129,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f126,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f43,f109])).

fof(f109,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f37])).

fof(f106,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f40,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f545,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f117,f543])).

fof(f543,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f542,f37])).

fof(f542,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f538,f38])).

fof(f538,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f495,f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f122,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f42,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f495,plain,(
    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f183,f470])).

fof(f470,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f435,f145])).

fof(f145,plain,(
    k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f144,f133])).

fof(f144,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f112,f141])).

fof(f141,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f64,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_tops_1(sK0,sK1),sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f111,f68])).

fof(f68,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f62,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f50,f49])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f53,f105])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f48,f93])).

fof(f93,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f92,f68])).

fof(f92,plain,
    ( sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f53,f90])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f56,f39])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f435,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f74,f411])).

fof(f411,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f141,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    inference(superposition,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f183,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f181,f41])).

fof(f181,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f94,f179])).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f70,f177])).

fof(f177,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f176,f81])).

fof(f81,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f74,f59])).

fof(f176,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f173,f70])).

fof(f173,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f94,f59])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f52,f59])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f55,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f117,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f116,f37])).

fof(f116,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f113,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:22:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (785874945)
% 0.13/0.37  ipcrm: permission denied for id (790265858)
% 0.13/0.37  ipcrm: permission denied for id (791773187)
% 0.13/0.37  ipcrm: permission denied for id (790331396)
% 0.13/0.37  ipcrm: permission denied for id (791805957)
% 0.13/0.38  ipcrm: permission denied for id (786333702)
% 0.13/0.38  ipcrm: permission denied for id (785907719)
% 0.13/0.38  ipcrm: permission denied for id (786366472)
% 0.13/0.38  ipcrm: permission denied for id (786399241)
% 0.13/0.38  ipcrm: permission denied for id (786432010)
% 0.13/0.38  ipcrm: permission denied for id (790396939)
% 0.13/0.38  ipcrm: permission denied for id (786497548)
% 0.13/0.38  ipcrm: permission denied for id (786530317)
% 0.13/0.39  ipcrm: permission denied for id (792821774)
% 0.13/0.39  ipcrm: permission denied for id (786595855)
% 0.13/0.39  ipcrm: permission denied for id (786628624)
% 0.13/0.39  ipcrm: permission denied for id (786661393)
% 0.13/0.39  ipcrm: permission denied for id (786694162)
% 0.13/0.39  ipcrm: permission denied for id (786726931)
% 0.13/0.39  ipcrm: permission denied for id (791871508)
% 0.13/0.39  ipcrm: permission denied for id (786792469)
% 0.13/0.40  ipcrm: permission denied for id (786858007)
% 0.13/0.40  ipcrm: permission denied for id (785940504)
% 0.13/0.40  ipcrm: permission denied for id (786890777)
% 0.13/0.40  ipcrm: permission denied for id (790560794)
% 0.13/0.40  ipcrm: permission denied for id (790593563)
% 0.13/0.40  ipcrm: permission denied for id (786989084)
% 0.13/0.40  ipcrm: permission denied for id (787021853)
% 0.13/0.41  ipcrm: permission denied for id (787054622)
% 0.13/0.41  ipcrm: permission denied for id (787087391)
% 0.13/0.41  ipcrm: permission denied for id (787120160)
% 0.13/0.41  ipcrm: permission denied for id (787152929)
% 0.13/0.41  ipcrm: permission denied for id (791937058)
% 0.13/0.41  ipcrm: permission denied for id (787218467)
% 0.13/0.41  ipcrm: permission denied for id (790659108)
% 0.13/0.41  ipcrm: permission denied for id (787284005)
% 0.13/0.42  ipcrm: permission denied for id (791969830)
% 0.13/0.42  ipcrm: permission denied for id (787349543)
% 0.20/0.42  ipcrm: permission denied for id (787382312)
% 0.20/0.42  ipcrm: permission denied for id (790724649)
% 0.20/0.42  ipcrm: permission denied for id (787447850)
% 0.20/0.42  ipcrm: permission denied for id (787480619)
% 0.20/0.42  ipcrm: permission denied for id (790757420)
% 0.20/0.42  ipcrm: permission denied for id (787546157)
% 0.20/0.43  ipcrm: permission denied for id (787578926)
% 0.20/0.43  ipcrm: permission denied for id (787611695)
% 0.20/0.43  ipcrm: permission denied for id (792002608)
% 0.20/0.43  ipcrm: permission denied for id (787677233)
% 0.20/0.43  ipcrm: permission denied for id (792035378)
% 0.20/0.43  ipcrm: permission denied for id (787742771)
% 0.20/0.43  ipcrm: permission denied for id (790855732)
% 0.20/0.43  ipcrm: permission denied for id (787808309)
% 0.20/0.44  ipcrm: permission denied for id (790888502)
% 0.20/0.44  ipcrm: permission denied for id (787873847)
% 0.20/0.44  ipcrm: permission denied for id (792068152)
% 0.20/0.44  ipcrm: permission denied for id (787939385)
% 0.20/0.44  ipcrm: permission denied for id (792100922)
% 0.20/0.44  ipcrm: permission denied for id (788004923)
% 0.20/0.44  ipcrm: permission denied for id (792133692)
% 0.20/0.45  ipcrm: permission denied for id (788070461)
% 0.20/0.45  ipcrm: permission denied for id (792166462)
% 0.20/0.45  ipcrm: permission denied for id (788135999)
% 0.20/0.45  ipcrm: permission denied for id (788168768)
% 0.20/0.45  ipcrm: permission denied for id (788201537)
% 0.20/0.45  ipcrm: permission denied for id (788234306)
% 0.20/0.45  ipcrm: permission denied for id (788267075)
% 0.20/0.45  ipcrm: permission denied for id (785973316)
% 0.20/0.46  ipcrm: permission denied for id (788299845)
% 0.20/0.46  ipcrm: permission denied for id (788332614)
% 0.20/0.46  ipcrm: permission denied for id (788365383)
% 0.20/0.46  ipcrm: permission denied for id (792887368)
% 0.20/0.46  ipcrm: permission denied for id (788430921)
% 0.20/0.46  ipcrm: permission denied for id (788463690)
% 0.20/0.46  ipcrm: permission denied for id (788496459)
% 0.20/0.47  ipcrm: permission denied for id (788529228)
% 0.20/0.47  ipcrm: permission denied for id (788561997)
% 0.20/0.47  ipcrm: permission denied for id (792952911)
% 0.20/0.47  ipcrm: permission denied for id (788725842)
% 0.20/0.47  ipcrm: permission denied for id (788758611)
% 0.20/0.48  ipcrm: permission denied for id (788791380)
% 0.20/0.48  ipcrm: permission denied for id (793051221)
% 0.20/0.48  ipcrm: permission denied for id (788856918)
% 0.20/0.48  ipcrm: permission denied for id (788922456)
% 0.20/0.48  ipcrm: permission denied for id (788955225)
% 0.20/0.48  ipcrm: permission denied for id (788987994)
% 0.20/0.49  ipcrm: permission denied for id (789020763)
% 0.20/0.49  ipcrm: permission denied for id (789053532)
% 0.20/0.49  ipcrm: permission denied for id (789086301)
% 0.20/0.49  ipcrm: permission denied for id (793116766)
% 0.20/0.49  ipcrm: permission denied for id (789151839)
% 0.20/0.49  ipcrm: permission denied for id (792461408)
% 0.20/0.49  ipcrm: permission denied for id (789217377)
% 0.20/0.50  ipcrm: permission denied for id (789282915)
% 0.20/0.50  ipcrm: permission denied for id (793182308)
% 0.20/0.50  ipcrm: permission denied for id (789348453)
% 0.20/0.50  ipcrm: permission denied for id (789413991)
% 0.20/0.50  ipcrm: permission denied for id (789446760)
% 0.20/0.50  ipcrm: permission denied for id (793247849)
% 0.20/0.50  ipcrm: permission denied for id (793280618)
% 0.20/0.51  ipcrm: permission denied for id (789545067)
% 0.20/0.51  ipcrm: permission denied for id (793313388)
% 0.20/0.51  ipcrm: permission denied for id (789610605)
% 0.20/0.51  ipcrm: permission denied for id (789643374)
% 0.20/0.51  ipcrm: permission denied for id (789676143)
% 0.20/0.51  ipcrm: permission denied for id (789708912)
% 0.20/0.51  ipcrm: permission denied for id (789741681)
% 0.20/0.51  ipcrm: permission denied for id (789774450)
% 0.20/0.52  ipcrm: permission denied for id (789839988)
% 0.20/0.52  ipcrm: permission denied for id (791576693)
% 0.20/0.52  ipcrm: permission denied for id (789905526)
% 0.20/0.52  ipcrm: permission denied for id (789971064)
% 0.20/0.52  ipcrm: permission denied for id (791642233)
% 0.20/0.52  ipcrm: permission denied for id (790036602)
% 0.20/0.53  ipcrm: permission denied for id (790102140)
% 0.20/0.53  ipcrm: permission denied for id (790134909)
% 0.20/0.53  ipcrm: permission denied for id (791707774)
% 0.20/0.53  ipcrm: permission denied for id (790200447)
% 0.77/0.61  % (18392)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.77/0.62  % (18395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.77/0.62  % (18404)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.77/0.63  % (18395)Refutation found. Thanks to Tanya!
% 0.77/0.63  % SZS status Theorem for theBenchmark
% 0.77/0.63  % SZS output start Proof for theBenchmark
% 0.77/0.63  fof(f546,plain,(
% 0.77/0.63    $false),
% 0.77/0.63    inference(subsumption_resolution,[],[f545,f133])).
% 0.77/0.63  fof(f133,plain,(
% 0.77/0.63    ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(trivial_inequality_removal,[],[f132])).
% 0.77/0.63  fof(f132,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(backward_demodulation,[],[f40,f131])).
% 0.77/0.63  fof(f131,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.77/0.63    inference(subsumption_resolution,[],[f130,f39])).
% 0.77/0.63  fof(f39,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(cnf_transformation,[],[f35])).
% 0.77/0.63  fof(f35,plain,(
% 0.77/0.63    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.77/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.77/0.63  fof(f33,plain,(
% 0.77/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.77/0.63    introduced(choice_axiom,[])).
% 0.77/0.63  fof(f34,plain,(
% 0.77/0.63    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.77/0.63    introduced(choice_axiom,[])).
% 0.77/0.63  fof(f32,plain,(
% 0.77/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.77/0.63    inference(flattening,[],[f31])).
% 0.77/0.63  fof(f31,plain,(
% 0.77/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.77/0.63    inference(nnf_transformation,[],[f20])).
% 0.77/0.63  fof(f20,plain,(
% 0.77/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.77/0.63    inference(flattening,[],[f19])).
% 0.77/0.63  fof(f19,plain,(
% 0.77/0.63    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.77/0.63    inference(ennf_transformation,[],[f18])).
% 0.77/0.63  fof(f18,negated_conjecture,(
% 0.77/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.77/0.63    inference(negated_conjecture,[],[f17])).
% 0.77/0.63  fof(f17,conjecture,(
% 0.77/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.77/0.63  fof(f130,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f129,f37])).
% 0.77/0.63  fof(f37,plain,(
% 0.77/0.63    l1_pre_topc(sK0)),
% 0.77/0.63    inference(cnf_transformation,[],[f35])).
% 0.77/0.63  fof(f129,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f126,f38])).
% 0.77/0.63  fof(f38,plain,(
% 0.77/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.77/0.63    inference(cnf_transformation,[],[f35])).
% 0.77/0.63  fof(f126,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(superposition,[],[f43,f109])).
% 0.77/0.63  fof(f109,plain,(
% 0.77/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f106,f37])).
% 0.77/0.63  fof(f106,plain,(
% 0.77/0.63    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.77/0.63    inference(resolution,[],[f44,f38])).
% 0.77/0.63  fof(f44,plain,(
% 0.77/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f24])).
% 0.77/0.63  fof(f24,plain,(
% 0.77/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.63    inference(flattening,[],[f23])).
% 0.77/0.63  fof(f23,plain,(
% 0.77/0.63    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.63    inference(ennf_transformation,[],[f13])).
% 0.77/0.63  fof(f13,axiom,(
% 0.77/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.77/0.63  fof(f43,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f22])).
% 0.77/0.63  fof(f22,plain,(
% 0.77/0.63    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.63    inference(ennf_transformation,[],[f15])).
% 0.77/0.63  fof(f15,axiom,(
% 0.77/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.77/0.63  fof(f40,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(cnf_transformation,[],[f35])).
% 0.77/0.63  fof(f545,plain,(
% 0.77/0.63    v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(trivial_inequality_removal,[],[f544])).
% 0.77/0.63  fof(f544,plain,(
% 0.77/0.63    sK1 != sK1 | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(backward_demodulation,[],[f117,f543])).
% 0.77/0.63  fof(f543,plain,(
% 0.77/0.63    sK1 = k2_pre_topc(sK0,sK1)),
% 0.77/0.63    inference(subsumption_resolution,[],[f542,f37])).
% 0.77/0.63  fof(f542,plain,(
% 0.77/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f538,f38])).
% 0.77/0.63  fof(f538,plain,(
% 0.77/0.63    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.77/0.63    inference(superposition,[],[f495,f123])).
% 0.77/0.63  fof(f123,plain,(
% 0.77/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.77/0.63    inference(subsumption_resolution,[],[f122,f54])).
% 0.77/0.63  fof(f54,plain,(
% 0.77/0.63    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f27])).
% 0.77/0.63  fof(f27,plain,(
% 0.77/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.77/0.63    inference(flattening,[],[f26])).
% 0.77/0.63  fof(f26,plain,(
% 0.77/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.77/0.63    inference(ennf_transformation,[],[f14])).
% 0.77/0.63  fof(f14,axiom,(
% 0.77/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.77/0.63  fof(f122,plain,(
% 0.77/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.77/0.63    inference(duplicate_literal_removal,[],[f119])).
% 0.77/0.63  fof(f119,plain,(
% 0.77/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.77/0.63    inference(superposition,[],[f42,f57])).
% 0.77/0.63  fof(f57,plain,(
% 0.77/0.63    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f30])).
% 0.77/0.63  fof(f30,plain,(
% 0.77/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.77/0.63    inference(flattening,[],[f29])).
% 0.77/0.63  fof(f29,plain,(
% 0.77/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.77/0.63    inference(ennf_transformation,[],[f10])).
% 0.77/0.63  fof(f10,axiom,(
% 0.77/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.77/0.63  fof(f42,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f21])).
% 0.77/0.63  fof(f21,plain,(
% 0.77/0.63    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.77/0.63    inference(ennf_transformation,[],[f16])).
% 0.77/0.63  fof(f16,axiom,(
% 0.77/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.77/0.63  fof(f495,plain,(
% 0.77/0.63    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.77/0.63    inference(superposition,[],[f183,f470])).
% 0.77/0.63  fof(f470,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.77/0.63    inference(superposition,[],[f435,f145])).
% 0.77/0.63  fof(f145,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.77/0.63    inference(subsumption_resolution,[],[f144,f133])).
% 0.77/0.63  fof(f144,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(backward_demodulation,[],[f112,f141])).
% 0.77/0.63  fof(f141,plain,(
% 0.77/0.63    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.77/0.63    inference(superposition,[],[f64,f51])).
% 0.77/0.63  fof(f51,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f12])).
% 0.77/0.63  fof(f12,axiom,(
% 0.77/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.77/0.63  fof(f64,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.77/0.63    inference(superposition,[],[f51,f49])).
% 0.77/0.63  fof(f49,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f8])).
% 0.77/0.63  fof(f8,axiom,(
% 0.77/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.77/0.63  fof(f112,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(forward_demodulation,[],[f111,f68])).
% 0.77/0.63  fof(f68,plain,(
% 0.77/0.63    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.77/0.63    inference(superposition,[],[f62,f50])).
% 0.77/0.63  fof(f50,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f9])).
% 0.77/0.63  fof(f9,axiom,(
% 0.77/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.77/0.63  fof(f62,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.77/0.63    inference(superposition,[],[f50,f49])).
% 0.77/0.63  fof(f111,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k2_xboole_0(k3_xboole_0(k2_tops_1(sK0,sK1),sK1),k1_xboole_0) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(superposition,[],[f53,f105])).
% 0.77/0.63  fof(f105,plain,(
% 0.77/0.63    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(superposition,[],[f48,f93])).
% 0.77/0.63  fof(f93,plain,(
% 0.77/0.63    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(forward_demodulation,[],[f92,f68])).
% 0.77/0.63  fof(f92,plain,(
% 0.77/0.63    sK1 = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(superposition,[],[f53,f90])).
% 0.77/0.63  fof(f90,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f87,f38])).
% 0.77/0.63  fof(f87,plain,(
% 0.77/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(superposition,[],[f56,f39])).
% 0.77/0.63  fof(f56,plain,(
% 0.77/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f28])).
% 0.77/0.63  fof(f28,plain,(
% 0.77/0.63    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.77/0.63    inference(ennf_transformation,[],[f11])).
% 0.77/0.63  fof(f11,axiom,(
% 0.77/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.77/0.63  fof(f48,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f5])).
% 0.77/0.63  fof(f5,axiom,(
% 0.77/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.77/0.63  fof(f53,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.77/0.63    inference(cnf_transformation,[],[f6])).
% 0.77/0.63  fof(f6,axiom,(
% 0.77/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.77/0.63  fof(f435,plain,(
% 0.77/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.77/0.63    inference(backward_demodulation,[],[f74,f411])).
% 0.77/0.63  fof(f411,plain,(
% 0.77/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.77/0.63    inference(superposition,[],[f141,f59])).
% 0.77/0.63  fof(f59,plain,(
% 0.77/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.77/0.63    inference(resolution,[],[f46,f47])).
% 0.77/0.63  fof(f47,plain,(
% 0.77/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f2])).
% 0.77/0.63  fof(f2,axiom,(
% 0.77/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.77/0.63  fof(f46,plain,(
% 0.77/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.77/0.63    inference(cnf_transformation,[],[f25])).
% 0.77/0.63  fof(f25,plain,(
% 0.77/0.63    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.77/0.63    inference(ennf_transformation,[],[f4])).
% 0.77/0.63  fof(f4,axiom,(
% 0.77/0.63    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.77/0.63  fof(f74,plain,(
% 0.77/0.63    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0) )),
% 0.77/0.63    inference(superposition,[],[f53,f41])).
% 0.77/0.63  fof(f41,plain,(
% 0.77/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.77/0.63    inference(cnf_transformation,[],[f3])).
% 0.77/0.63  fof(f3,axiom,(
% 0.77/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.77/0.63  fof(f183,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.77/0.63    inference(forward_demodulation,[],[f181,f41])).
% 0.77/0.63  fof(f181,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.77/0.63    inference(backward_demodulation,[],[f94,f179])).
% 0.77/0.63  fof(f179,plain,(
% 0.77/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.77/0.63    inference(backward_demodulation,[],[f70,f177])).
% 0.77/0.63  fof(f177,plain,(
% 0.77/0.63    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.77/0.63    inference(forward_demodulation,[],[f176,f81])).
% 0.77/0.63  fof(f81,plain,(
% 0.77/0.63    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.77/0.63    inference(superposition,[],[f74,f59])).
% 0.77/0.63  fof(f176,plain,(
% 0.77/0.63    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.77/0.63    inference(forward_demodulation,[],[f173,f70])).
% 0.77/0.63  fof(f173,plain,(
% 0.77/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.77/0.63    inference(superposition,[],[f94,f59])).
% 0.77/0.63  fof(f70,plain,(
% 0.77/0.63    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.77/0.63    inference(superposition,[],[f52,f59])).
% 0.77/0.63  fof(f52,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f1])).
% 0.77/0.63  fof(f1,axiom,(
% 0.77/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.77/0.63  fof(f94,plain,(
% 0.77/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.77/0.63    inference(superposition,[],[f55,f41])).
% 0.77/0.63  fof(f55,plain,(
% 0.77/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.77/0.63    inference(cnf_transformation,[],[f7])).
% 0.77/0.63  fof(f7,axiom,(
% 0.77/0.63    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.77/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.77/0.63  fof(f117,plain,(
% 0.77/0.63    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f116,f37])).
% 0.77/0.63  fof(f116,plain,(
% 0.77/0.63    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.77/0.63    inference(subsumption_resolution,[],[f113,f36])).
% 0.77/0.63  fof(f36,plain,(
% 0.77/0.63    v2_pre_topc(sK0)),
% 0.77/0.63    inference(cnf_transformation,[],[f35])).
% 0.77/0.63  fof(f113,plain,(
% 0.77/0.63    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.77/0.63    inference(resolution,[],[f45,f38])).
% 0.77/0.63  fof(f45,plain,(
% 0.77/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.77/0.63    inference(cnf_transformation,[],[f24])).
% 0.77/0.63  % SZS output end Proof for theBenchmark
% 0.77/0.63  % (18395)------------------------------
% 0.77/0.63  % (18395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.77/0.63  % (18395)Termination reason: Refutation
% 0.77/0.63  
% 0.77/0.63  % (18395)Memory used [KB]: 2046
% 0.77/0.63  % (18395)Time elapsed: 0.047 s
% 0.77/0.63  % (18395)------------------------------
% 0.77/0.63  % (18395)------------------------------
% 0.77/0.63  % (18168)Success in time 0.27 s
%------------------------------------------------------------------------------
