%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:49 EST 2020

% Result     : Theorem 4.33s
% Output     : Refutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  135 (1142 expanded)
%              Number of leaves         :   21 ( 302 expanded)
%              Depth                    :   30
%              Number of atoms          :  320 (5196 expanded)
%              Number of equality atoms :  128 (1576 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5630,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5629,f5603])).

fof(f5603,plain,(
    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f5602,f112])).

fof(f112,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f53,f109])).

fof(f109,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f53,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f5602,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f5599])).

fof(f5599,plain,
    ( sK1 != sK1
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f139,f5598])).

fof(f5598,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f5595])).

fof(f5595,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f1095,f2181])).

fof(f2181,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f1010,f2131])).

fof(f2131,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f2113,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2113,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f65,f542])).

fof(f542,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f157,f196])).

fof(f196,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,k1_xboole_0),X5) ),
    inference(resolution,[],[f108,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    ! [X2,X1] : m1_subset_1(k3_xboole_0(X2,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(backward_demodulation,[],[f104,f106])).

fof(f106,plain,(
    ! [X2,X1] : k9_subset_1(X1,X2,k1_xboole_0) = k3_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f75,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f104,plain,(
    ! [X2,X1] : m1_subset_1(k9_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f72,f54])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1010,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f64,f344])).

fof(f344,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f343,f177])).

fof(f177,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f174,f171])).

fof(f171,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f160,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f97,f95])).

fof(f95,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f94,f55])).

fof(f94,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f67,f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f68,f54])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f160,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f84,f67])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f73,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f174,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f65,f88])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f66,f78])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f343,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f65,f217])).

fof(f217,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f89,f116])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f58,f111])).

fof(f111,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f52,f109])).

fof(f52,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f89,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f66,f61])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1095,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f1090,f154])).

fof(f154,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f126,f51])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1090,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f395,f217])).

fof(f395,plain,(
    ! [X13] : k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(X13,sK1)) = k2_xboole_0(sK1,k3_xboole_0(X13,sK1)) ),
    inference(resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X9,k3_xboole_0(X10,sK1)) = k2_xboole_0(X9,k3_xboole_0(X10,sK1)) ) ),
    inference(resolution,[],[f107,f77])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f103,f105])).

fof(f105,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(resolution,[],[f75,f51])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f74,f51])).

fof(f139,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f124,f51])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) != X0 ) ),
    inference(subsumption_resolution,[],[f123,f50])).

fof(f123,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) != X0
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5629,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f853,f5628])).

fof(f5628,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f5613,f5626])).

fof(f5626,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f5612,f283])).

fof(f283,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f151,f109])).

fof(f151,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f125,f51])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f5612,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f5610,f67])).

fof(f5610,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f5607,f73])).

fof(f5607,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f5606,f50])).

fof(f5606,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5604,f51])).

fof(f5604,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f5602,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f5613,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f5610,f68])).

fof(f853,plain,(
    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f179,f283])).

fof(f179,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f85,f67])).

fof(f85,plain,(
    ! [X2,X1] : m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f73,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (7553)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.48  % (7546)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7541)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (7543)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (7549)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (7540)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (7552)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (7551)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (7562)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (7563)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (7557)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (7569)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (7550)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (7568)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (7569)Refutation not found, incomplete strategy% (7569)------------------------------
% 0.21/0.53  % (7569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7569)Memory used [KB]: 1663
% 0.21/0.53  % (7569)Time elapsed: 0.122 s
% 0.21/0.53  % (7569)------------------------------
% 0.21/0.53  % (7569)------------------------------
% 0.21/0.53  % (7541)Refutation not found, incomplete strategy% (7541)------------------------------
% 0.21/0.53  % (7541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7541)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7541)Memory used [KB]: 1791
% 0.21/0.53  % (7541)Time elapsed: 0.128 s
% 0.21/0.53  % (7541)------------------------------
% 0.21/0.53  % (7541)------------------------------
% 0.21/0.53  % (7564)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (7568)Refutation not found, incomplete strategy% (7568)------------------------------
% 0.21/0.53  % (7568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7555)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (7560)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (7542)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7554)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (7545)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7552)Refutation not found, incomplete strategy% (7552)------------------------------
% 0.21/0.54  % (7552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7544)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (7554)Refutation not found, incomplete strategy% (7554)------------------------------
% 0.21/0.54  % (7554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7568)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7568)Memory used [KB]: 10746
% 0.21/0.54  % (7568)Time elapsed: 0.118 s
% 0.21/0.54  % (7568)------------------------------
% 0.21/0.54  % (7568)------------------------------
% 0.21/0.54  % (7547)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (7552)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7552)Memory used [KB]: 10874
% 0.21/0.54  % (7552)Time elapsed: 0.114 s
% 0.21/0.54  % (7552)------------------------------
% 0.21/0.54  % (7552)------------------------------
% 0.21/0.55  % (7561)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (7556)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (7556)Refutation not found, incomplete strategy% (7556)------------------------------
% 0.21/0.55  % (7556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7556)Memory used [KB]: 10618
% 0.21/0.55  % (7556)Time elapsed: 0.147 s
% 0.21/0.55  % (7556)------------------------------
% 0.21/0.55  % (7556)------------------------------
% 0.21/0.55  % (7554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7554)Memory used [KB]: 1791
% 0.21/0.55  % (7554)Time elapsed: 0.128 s
% 0.21/0.55  % (7554)------------------------------
% 0.21/0.55  % (7554)------------------------------
% 0.21/0.55  % (7558)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (7548)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (7565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (7550)Refutation not found, incomplete strategy% (7550)------------------------------
% 0.21/0.55  % (7550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7550)Memory used [KB]: 10746
% 0.21/0.55  % (7550)Time elapsed: 0.149 s
% 0.21/0.55  % (7550)------------------------------
% 0.21/0.55  % (7550)------------------------------
% 0.21/0.56  % (7566)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (7567)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (7566)Refutation not found, incomplete strategy% (7566)------------------------------
% 0.21/0.56  % (7566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7566)Memory used [KB]: 6524
% 0.21/0.56  % (7566)Time elapsed: 0.158 s
% 0.21/0.56  % (7566)------------------------------
% 0.21/0.56  % (7566)------------------------------
% 0.21/0.57  % (7559)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.07/0.64  % (7571)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.07/0.67  % (7573)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.07/0.67  % (7570)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.07/0.70  % (7575)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.07/0.71  % (7574)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.07/0.72  % (7543)Refutation not found, incomplete strategy% (7543)------------------------------
% 2.07/0.72  % (7543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.72  % (7543)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.72  
% 2.07/0.72  % (7543)Memory used [KB]: 6268
% 2.07/0.72  % (7543)Time elapsed: 0.295 s
% 2.07/0.72  % (7543)------------------------------
% 2.07/0.72  % (7543)------------------------------
% 2.80/0.72  % (7577)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.80/0.73  % (7572)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.80/0.73  % (7572)Refutation not found, incomplete strategy% (7572)------------------------------
% 2.80/0.73  % (7572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.73  % (7572)Termination reason: Refutation not found, incomplete strategy
% 2.80/0.73  
% 2.80/0.73  % (7572)Memory used [KB]: 6268
% 2.80/0.73  % (7572)Time elapsed: 0.160 s
% 2.80/0.73  % (7572)------------------------------
% 2.80/0.73  % (7572)------------------------------
% 2.80/0.74  % (7576)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.39/0.81  % (7564)Time limit reached!
% 3.39/0.81  % (7564)------------------------------
% 3.39/0.81  % (7564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.81  % (7564)Termination reason: Time limit
% 3.39/0.81  
% 3.39/0.81  % (7564)Memory used [KB]: 13432
% 3.39/0.81  % (7564)Time elapsed: 0.408 s
% 3.39/0.81  % (7564)------------------------------
% 3.39/0.81  % (7564)------------------------------
% 3.39/0.82  % (7542)Time limit reached!
% 3.39/0.82  % (7542)------------------------------
% 3.39/0.82  % (7542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.82  % (7542)Termination reason: Time limit
% 3.39/0.82  % (7542)Termination phase: Saturation
% 3.39/0.82  
% 3.39/0.82  % (7542)Memory used [KB]: 6908
% 3.39/0.82  % (7542)Time elapsed: 0.400 s
% 3.39/0.82  % (7542)------------------------------
% 3.39/0.82  % (7542)------------------------------
% 3.95/0.88  % (7540)Refutation not found, incomplete strategy% (7540)------------------------------
% 3.95/0.88  % (7540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.88  % (7540)Termination reason: Refutation not found, incomplete strategy
% 3.95/0.88  
% 3.95/0.88  % (7540)Memory used [KB]: 2302
% 3.95/0.88  % (7540)Time elapsed: 0.457 s
% 3.95/0.88  % (7540)------------------------------
% 3.95/0.88  % (7540)------------------------------
% 3.95/0.88  % (7578)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.95/0.90  % (7579)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.33/0.94  % (7580)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.33/0.95  % (7547)Refutation found. Thanks to Tanya!
% 4.33/0.95  % SZS status Theorem for theBenchmark
% 4.33/0.95  % SZS output start Proof for theBenchmark
% 4.33/0.95  fof(f5630,plain,(
% 4.33/0.95    $false),
% 4.33/0.95    inference(subsumption_resolution,[],[f5629,f5603])).
% 4.33/0.95  fof(f5603,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(resolution,[],[f5602,f112])).
% 4.33/0.95  fof(f112,plain,(
% 4.33/0.95    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(backward_demodulation,[],[f53,f109])).
% 4.33/0.95  fof(f109,plain,(
% 4.33/0.95    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 4.33/0.95    inference(resolution,[],[f76,f51])).
% 4.33/0.95  fof(f51,plain,(
% 4.33/0.95    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.33/0.95    inference(cnf_transformation,[],[f45])).
% 4.33/0.95  fof(f45,plain,(
% 4.33/0.95    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.33/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 4.33/0.95  fof(f43,plain,(
% 4.33/0.95    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.33/0.95    introduced(choice_axiom,[])).
% 4.33/0.95  fof(f44,plain,(
% 4.33/0.95    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.33/0.95    introduced(choice_axiom,[])).
% 4.33/0.95  fof(f42,plain,(
% 4.33/0.95    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.33/0.95    inference(flattening,[],[f41])).
% 4.33/0.95  fof(f41,plain,(
% 4.33/0.95    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.33/0.95    inference(nnf_transformation,[],[f26])).
% 4.33/0.95  fof(f26,plain,(
% 4.33/0.95    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.33/0.95    inference(flattening,[],[f25])).
% 4.33/0.95  fof(f25,plain,(
% 4.33/0.95    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f23])).
% 4.33/0.95  fof(f23,negated_conjecture,(
% 4.33/0.95    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 4.33/0.95    inference(negated_conjecture,[],[f22])).
% 4.33/0.95  fof(f22,conjecture,(
% 4.33/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 4.33/0.95  fof(f76,plain,(
% 4.33/0.95    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f38])).
% 4.33/0.95  fof(f38,plain,(
% 4.33/0.95    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f12])).
% 4.33/0.95  fof(f12,axiom,(
% 4.33/0.95    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 4.33/0.95  fof(f53,plain,(
% 4.33/0.95    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(cnf_transformation,[],[f45])).
% 4.33/0.95  fof(f5602,plain,(
% 4.33/0.95    v4_pre_topc(sK1,sK0)),
% 4.33/0.95    inference(trivial_inequality_removal,[],[f5599])).
% 4.33/0.95  fof(f5599,plain,(
% 4.33/0.95    sK1 != sK1 | v4_pre_topc(sK1,sK0)),
% 4.33/0.95    inference(backward_demodulation,[],[f139,f5598])).
% 4.33/0.95  fof(f5598,plain,(
% 4.33/0.95    sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(duplicate_literal_removal,[],[f5595])).
% 4.33/0.95  fof(f5595,plain,(
% 4.33/0.95    sK1 = k2_pre_topc(sK0,sK1) | sK1 = k2_pre_topc(sK0,sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(superposition,[],[f1095,f2181])).
% 4.33/0.95  fof(f2181,plain,(
% 4.33/0.95    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(backward_demodulation,[],[f1010,f2131])).
% 4.33/0.95  fof(f2131,plain,(
% 4.33/0.95    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 4.33/0.95    inference(forward_demodulation,[],[f2113,f55])).
% 4.33/0.95  fof(f55,plain,(
% 4.33/0.95    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.33/0.95    inference(cnf_transformation,[],[f5])).
% 4.33/0.95  fof(f5,axiom,(
% 4.33/0.95    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 4.33/0.95  fof(f2113,plain,(
% 4.33/0.95    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0)) )),
% 4.33/0.95    inference(superposition,[],[f65,f542])).
% 4.33/0.95  fof(f542,plain,(
% 4.33/0.95    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 4.33/0.95    inference(resolution,[],[f157,f196])).
% 4.33/0.95  fof(f196,plain,(
% 4.33/0.95    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,k1_xboole_0),X5)) )),
% 4.33/0.95    inference(resolution,[],[f108,f72])).
% 4.33/0.95  fof(f72,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f48])).
% 4.33/0.95  fof(f48,plain,(
% 4.33/0.95    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.33/0.95    inference(nnf_transformation,[],[f16])).
% 4.33/0.95  fof(f16,axiom,(
% 4.33/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.33/0.95  fof(f108,plain,(
% 4.33/0.95    ( ! [X2,X1] : (m1_subset_1(k3_xboole_0(X2,k1_xboole_0),k1_zfmisc_1(X1))) )),
% 4.33/0.95    inference(backward_demodulation,[],[f104,f106])).
% 4.33/0.95  fof(f106,plain,(
% 4.33/0.95    ( ! [X2,X1] : (k9_subset_1(X1,X2,k1_xboole_0) = k3_xboole_0(X2,k1_xboole_0)) )),
% 4.33/0.95    inference(resolution,[],[f75,f54])).
% 4.33/0.95  fof(f54,plain,(
% 4.33/0.95    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f14])).
% 4.33/0.95  fof(f14,axiom,(
% 4.33/0.95    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 4.33/0.95  fof(f75,plain,(
% 4.33/0.95    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f37])).
% 4.33/0.95  fof(f37,plain,(
% 4.33/0.95    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f13])).
% 4.33/0.95  fof(f13,axiom,(
% 4.33/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 4.33/0.95  fof(f104,plain,(
% 4.33/0.95    ( ! [X2,X1] : (m1_subset_1(k9_subset_1(X1,X2,k1_xboole_0),k1_zfmisc_1(X1))) )),
% 4.33/0.95    inference(resolution,[],[f74,f54])).
% 4.33/0.95  fof(f74,plain,(
% 4.33/0.95    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f36])).
% 4.33/0.95  fof(f36,plain,(
% 4.33/0.95    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f9])).
% 4.33/0.95  fof(f9,axiom,(
% 4.33/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 4.33/0.95  fof(f157,plain,(
% 4.33/0.95    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 4.33/0.95    inference(resolution,[],[f83,f71])).
% 4.33/0.95  fof(f71,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f47])).
% 4.33/0.95  fof(f47,plain,(
% 4.33/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.33/0.95    inference(flattening,[],[f46])).
% 4.33/0.95  fof(f46,plain,(
% 4.33/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.33/0.95    inference(nnf_transformation,[],[f1])).
% 4.33/0.95  fof(f1,axiom,(
% 4.33/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.33/0.95  fof(f83,plain,(
% 4.33/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.33/0.95    inference(resolution,[],[f72,f54])).
% 4.33/0.95  fof(f65,plain,(
% 4.33/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f2])).
% 4.33/0.95  fof(f2,axiom,(
% 4.33/0.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.33/0.95  fof(f1010,plain,(
% 4.33/0.95    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(superposition,[],[f64,f344])).
% 4.33/0.95  fof(f344,plain,(
% 4.33/0.95    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(forward_demodulation,[],[f343,f177])).
% 4.33/0.95  fof(f177,plain,(
% 4.33/0.95    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.33/0.95    inference(forward_demodulation,[],[f174,f171])).
% 4.33/0.95  fof(f171,plain,(
% 4.33/0.95    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.33/0.95    inference(forward_demodulation,[],[f160,f99])).
% 4.33/0.95  fof(f99,plain,(
% 4.33/0.95    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 4.33/0.95    inference(forward_demodulation,[],[f97,f95])).
% 4.33/0.95  fof(f95,plain,(
% 4.33/0.95    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 4.33/0.95    inference(forward_demodulation,[],[f94,f55])).
% 4.33/0.95  fof(f94,plain,(
% 4.33/0.95    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 4.33/0.95    inference(resolution,[],[f67,f54])).
% 4.33/0.95  fof(f67,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f34])).
% 4.33/0.95  fof(f34,plain,(
% 4.33/0.95    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f8])).
% 4.33/0.95  fof(f8,axiom,(
% 4.33/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 4.33/0.95  fof(f97,plain,(
% 4.33/0.95    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 4.33/0.95    inference(resolution,[],[f68,f54])).
% 4.33/0.95  fof(f68,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 4.33/0.95    inference(cnf_transformation,[],[f35])).
% 4.33/0.95  fof(f35,plain,(
% 4.33/0.95    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(ennf_transformation,[],[f10])).
% 4.33/0.95  fof(f10,axiom,(
% 4.33/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 4.33/0.95  fof(f160,plain,(
% 4.33/0.95    ( ! [X0] : (k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)) )),
% 4.33/0.95    inference(resolution,[],[f84,f67])).
% 4.33/0.95  fof(f84,plain,(
% 4.33/0.95    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 4.33/0.95    inference(resolution,[],[f73,f78])).
% 4.33/0.95  fof(f78,plain,(
% 4.33/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.33/0.95    inference(equality_resolution,[],[f70])).
% 4.33/0.95  fof(f70,plain,(
% 4.33/0.95    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.33/0.95    inference(cnf_transformation,[],[f47])).
% 4.33/0.95  fof(f73,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f48])).
% 4.33/0.95  fof(f174,plain,(
% 4.33/0.95    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 4.33/0.95    inference(superposition,[],[f65,f88])).
% 4.33/0.95  fof(f88,plain,(
% 4.33/0.95    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.33/0.95    inference(resolution,[],[f66,f78])).
% 4.33/0.95  fof(f66,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.33/0.95    inference(cnf_transformation,[],[f33])).
% 4.33/0.95  fof(f33,plain,(
% 4.33/0.95    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.33/0.95    inference(ennf_transformation,[],[f3])).
% 4.33/0.95  fof(f3,axiom,(
% 4.33/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.33/0.95  fof(f343,plain,(
% 4.33/0.95    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(superposition,[],[f65,f217])).
% 4.33/0.95  fof(f217,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(superposition,[],[f89,f116])).
% 4.33/0.95  fof(f116,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(subsumption_resolution,[],[f115,f50])).
% 4.33/0.95  fof(f50,plain,(
% 4.33/0.95    l1_pre_topc(sK0)),
% 4.33/0.95    inference(cnf_transformation,[],[f45])).
% 4.33/0.95  fof(f115,plain,(
% 4.33/0.95    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(subsumption_resolution,[],[f114,f51])).
% 4.33/0.95  fof(f114,plain,(
% 4.33/0.95    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(resolution,[],[f58,f111])).
% 4.33/0.95  fof(f111,plain,(
% 4.33/0.95    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(backward_demodulation,[],[f52,f109])).
% 4.33/0.95  fof(f52,plain,(
% 4.33/0.95    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(cnf_transformation,[],[f45])).
% 4.33/0.95  fof(f58,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f30])).
% 4.33/0.95  fof(f30,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(flattening,[],[f29])).
% 4.33/0.95  fof(f29,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(ennf_transformation,[],[f18])).
% 4.33/0.95  fof(f18,axiom,(
% 4.33/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 4.33/0.95  fof(f89,plain,(
% 4.33/0.95    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 4.33/0.95    inference(resolution,[],[f66,f61])).
% 4.33/0.95  fof(f61,plain,(
% 4.33/0.95    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f4])).
% 4.33/0.95  fof(f4,axiom,(
% 4.33/0.95    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.33/0.95  fof(f64,plain,(
% 4.33/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f6])).
% 4.33/0.95  fof(f6,axiom,(
% 4.33/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.33/0.95  fof(f1095,plain,(
% 4.33/0.95    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(forward_demodulation,[],[f1090,f154])).
% 4.33/0.95  fof(f154,plain,(
% 4.33/0.95    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 4.33/0.95    inference(resolution,[],[f126,f51])).
% 4.33/0.95  fof(f126,plain,(
% 4.33/0.95    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 4.33/0.95    inference(resolution,[],[f57,f50])).
% 4.33/0.95  fof(f57,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f28])).
% 4.33/0.95  fof(f28,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(ennf_transformation,[],[f19])).
% 4.33/0.95  fof(f19,axiom,(
% 4.33/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 4.33/0.95  fof(f1090,plain,(
% 4.33/0.95    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 4.33/0.95    inference(superposition,[],[f395,f217])).
% 4.33/0.95  fof(f395,plain,(
% 4.33/0.95    ( ! [X13] : (k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(X13,sK1)) = k2_xboole_0(sK1,k3_xboole_0(X13,sK1))) )),
% 4.33/0.95    inference(resolution,[],[f133,f51])).
% 4.33/0.95  fof(f133,plain,(
% 4.33/0.95    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X9,k3_xboole_0(X10,sK1)) = k2_xboole_0(X9,k3_xboole_0(X10,sK1))) )),
% 4.33/0.95    inference(resolution,[],[f107,f77])).
% 4.33/0.95  fof(f77,plain,(
% 4.33/0.95    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f40])).
% 4.33/0.95  fof(f40,plain,(
% 4.33/0.95    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.33/0.95    inference(flattening,[],[f39])).
% 4.33/0.95  fof(f39,plain,(
% 4.33/0.95    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.33/0.95    inference(ennf_transformation,[],[f11])).
% 4.33/0.95  fof(f11,axiom,(
% 4.33/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 4.33/0.95  fof(f107,plain,(
% 4.33/0.95    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 4.33/0.95    inference(backward_demodulation,[],[f103,f105])).
% 4.33/0.95  fof(f105,plain,(
% 4.33/0.95    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) )),
% 4.33/0.95    inference(resolution,[],[f75,f51])).
% 4.33/0.95  fof(f103,plain,(
% 4.33/0.95    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 4.33/0.95    inference(resolution,[],[f74,f51])).
% 4.33/0.95  fof(f139,plain,(
% 4.33/0.95    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 4.33/0.95    inference(resolution,[],[f124,f51])).
% 4.33/0.95  fof(f124,plain,(
% 4.33/0.95    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) != X0) )),
% 4.33/0.95    inference(subsumption_resolution,[],[f123,f50])).
% 4.33/0.95  fof(f123,plain,(
% 4.33/0.95    ( ! [X0] : (k2_pre_topc(sK0,X0) != X0 | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 4.33/0.95    inference(resolution,[],[f59,f49])).
% 4.33/0.95  fof(f49,plain,(
% 4.33/0.95    v2_pre_topc(sK0)),
% 4.33/0.95    inference(cnf_transformation,[],[f45])).
% 4.33/0.95  fof(f59,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f30])).
% 4.33/0.95  fof(f5629,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(backward_demodulation,[],[f853,f5628])).
% 4.33/0.95  fof(f5628,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(forward_demodulation,[],[f5613,f5626])).
% 4.33/0.95  fof(f5626,plain,(
% 4.33/0.95    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 4.33/0.95    inference(forward_demodulation,[],[f5612,f283])).
% 4.33/0.95  fof(f283,plain,(
% 4.33/0.95    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 4.33/0.95    inference(superposition,[],[f151,f109])).
% 4.33/0.95  fof(f151,plain,(
% 4.33/0.95    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 4.33/0.95    inference(resolution,[],[f125,f51])).
% 4.33/0.95  fof(f125,plain,(
% 4.33/0.95    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 4.33/0.95    inference(resolution,[],[f56,f50])).
% 4.33/0.95  fof(f56,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 4.33/0.95    inference(cnf_transformation,[],[f27])).
% 4.33/0.95  fof(f27,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(ennf_transformation,[],[f21])).
% 4.33/0.95  fof(f21,axiom,(
% 4.33/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 4.33/0.95  fof(f5612,plain,(
% 4.33/0.95    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 4.33/0.95    inference(resolution,[],[f5610,f67])).
% 4.33/0.95  fof(f5610,plain,(
% 4.33/0.95    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 4.33/0.95    inference(resolution,[],[f5607,f73])).
% 4.33/0.95  fof(f5607,plain,(
% 4.33/0.95    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 4.33/0.95    inference(subsumption_resolution,[],[f5606,f50])).
% 4.33/0.95  fof(f5606,plain,(
% 4.33/0.95    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 4.33/0.95    inference(subsumption_resolution,[],[f5604,f51])).
% 4.33/0.95  fof(f5604,plain,(
% 4.33/0.95    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 4.33/0.95    inference(resolution,[],[f5602,f60])).
% 4.33/0.95  fof(f60,plain,(
% 4.33/0.95    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.33/0.95    inference(cnf_transformation,[],[f32])).
% 4.33/0.95  fof(f32,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(flattening,[],[f31])).
% 4.33/0.95  fof(f31,plain,(
% 4.33/0.95    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.33/0.95    inference(ennf_transformation,[],[f20])).
% 4.33/0.95  fof(f20,axiom,(
% 4.33/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 4.33/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 4.33/0.95  fof(f5613,plain,(
% 4.33/0.95    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 4.33/0.95    inference(resolution,[],[f5610,f68])).
% 4.33/0.95  fof(f853,plain,(
% 4.33/0.95    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 4.33/0.95    inference(superposition,[],[f179,f283])).
% 4.33/0.95  fof(f179,plain,(
% 4.33/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 4.33/0.95    inference(resolution,[],[f85,f67])).
% 4.33/0.95  fof(f85,plain,(
% 4.33/0.95    ( ! [X2,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))) )),
% 4.33/0.95    inference(resolution,[],[f73,f61])).
% 4.33/0.95  % SZS output end Proof for theBenchmark
% 4.33/0.95  % (7547)------------------------------
% 4.33/0.95  % (7547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.95  % (7547)Termination reason: Refutation
% 4.33/0.95  
% 4.33/0.95  % (7547)Memory used [KB]: 6140
% 4.33/0.95  % (7547)Time elapsed: 0.530 s
% 4.33/0.95  % (7547)------------------------------
% 4.33/0.95  % (7547)------------------------------
% 4.33/0.95  % (7539)Success in time 0.583 s
%------------------------------------------------------------------------------
