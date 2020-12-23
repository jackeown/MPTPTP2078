%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 (1177 expanded)
%              Number of leaves         :   17 ( 368 expanded)
%              Depth                    :   25
%              Number of atoms          :  341 (7203 expanded)
%              Number of equality atoms :   97 (1223 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f387,f81])).

fof(f81,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(forward_demodulation,[],[f80,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f80,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(backward_demodulation,[],[f78,f79])).

fof(f79,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(backward_demodulation,[],[f75,f76])).

fof(f76,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK0),X1,sK1) = k1_setfam_1(k2_tarski(X1,sK1)) ),
    inference(resolution,[],[f72,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f40,f71])).

fof(f71,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f78,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f74,f75])).

fof(f74,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(backward_demodulation,[],[f44,f71])).

fof(f44,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f387,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(forward_demodulation,[],[f386,f296])).

fof(f296,plain,(
    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f295,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f295,plain,(
    k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f65,f244])).

fof(f244,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f199,f224])).

fof(f224,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f219,f113])).

fof(f113,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X1] :
      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = X1
      | r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1)
      | r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 ) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,k2_struct_0(sK0),X3),sK1)
      | k4_xboole_0(X2,k2_struct_0(sK0)) = X3
      | r2_hidden(sK3(X2,k2_struct_0(sK0),X3),X3) ) ),
    inference(resolution,[],[f77,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_struct_0(sK0))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f219,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f201,f46])).

fof(f201,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f177,f163])).

fof(f163,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f126,f125])).

fof(f125,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(sK1,k2_struct_0(sK0),k4_xboole_0(X1,X2)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(sK1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f113,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK3(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4)
      | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f113,f68])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f177,plain,(
    ! [X5] : ~ r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f174,f173])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(sK1,k2_struct_0(sK0)))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f69,f163])).

fof(f174,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0)))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f68,f163])).

fof(f199,plain,(
    k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f177,f119])).

fof(f119,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK2,k2_struct_0(sK0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X1] :
      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = X1
      | r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1)
      | r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1)
      | k4_xboole_0(sK2,k2_struct_0(sK0)) = X1 ) ),
    inference(resolution,[],[f94,f62])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,k2_struct_0(sK0),X3),sK2)
      | k4_xboole_0(X2,k2_struct_0(sK0)) = X3
      | r2_hidden(sK3(X2,k2_struct_0(sK0),X3),X3) ) ),
    inference(resolution,[],[f84,f63])).

fof(f84,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_struct_0(sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f73,f55])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f42,f71])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f386,plain,(
    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f384,f101])).

fof(f101,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f41,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f90,f72])).

fof(f90,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f39])).

fof(f87,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X2,sK0)
      | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f49,f71])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f384,plain,(
    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f194,f72])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,X1)))) ) ),
    inference(forward_demodulation,[],[f193,f52])).

fof(f193,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X1),sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f192,f85])).

fof(f85,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(backward_demodulation,[],[f82,f83])).

fof(f83,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2)) ),
    inference(resolution,[],[f73,f66])).

fof(f82,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0) ),
    inference(resolution,[],[f73,f58])).

fof(f192,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f191,f85])).

fof(f191,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f179,f43])).

fof(f43,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f179,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(sK2,sK0)
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f89,f73])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f51,f71])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.33  % Computer   : n014.cluster.edu
% 0.15/0.33  % Model      : x86_64 x86_64
% 0.15/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.33  % Memory     : 8042.1875MB
% 0.15/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.33  % CPULimit   : 60
% 0.15/0.33  % WCLimit    : 600
% 0.15/0.33  % DateTime   : Tue Dec  1 16:28:07 EST 2020
% 0.15/0.33  % CPUTime    : 
% 0.20/0.47  % (13730)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.48  % (13743)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.49  % (13746)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (13742)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (13749)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (13750)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (13733)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (13726)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (13749)Refutation not found, incomplete strategy% (13749)------------------------------
% 0.20/0.50  % (13749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13749)Memory used [KB]: 10746
% 0.20/0.50  % (13749)Time elapsed: 0.065 s
% 0.20/0.50  % (13749)------------------------------
% 0.20/0.50  % (13749)------------------------------
% 0.20/0.50  % (13726)Refutation not found, incomplete strategy% (13726)------------------------------
% 0.20/0.50  % (13726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13726)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13726)Memory used [KB]: 1791
% 0.20/0.50  % (13726)Time elapsed: 0.077 s
% 0.20/0.50  % (13726)------------------------------
% 0.20/0.50  % (13726)------------------------------
% 0.20/0.51  % (13754)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (13727)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (13728)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13738)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (13728)Refutation not found, incomplete strategy% (13728)------------------------------
% 0.20/0.52  % (13728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13728)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13728)Memory used [KB]: 10874
% 0.20/0.52  % (13728)Time elapsed: 0.126 s
% 0.20/0.52  % (13728)------------------------------
% 0.20/0.52  % (13728)------------------------------
% 0.20/0.52  % (13734)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13744)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (13755)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (13731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (13745)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (13736)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (13747)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (13737)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (13753)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (13737)Refutation not found, incomplete strategy% (13737)------------------------------
% 0.20/0.54  % (13737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13737)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13737)Memory used [KB]: 10746
% 0.20/0.54  % (13737)Time elapsed: 0.140 s
% 0.20/0.54  % (13737)------------------------------
% 0.20/0.54  % (13737)------------------------------
% 0.20/0.54  % (13747)Refutation not found, incomplete strategy% (13747)------------------------------
% 0.20/0.54  % (13747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13747)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13747)Memory used [KB]: 10874
% 0.20/0.54  % (13747)Time elapsed: 0.139 s
% 0.20/0.54  % (13747)------------------------------
% 0.20/0.54  % (13747)------------------------------
% 0.20/0.54  % (13752)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (13738)Refutation not found, incomplete strategy% (13738)------------------------------
% 0.20/0.54  % (13738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13738)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13738)Memory used [KB]: 10746
% 0.20/0.54  % (13738)Time elapsed: 0.145 s
% 0.20/0.54  % (13738)------------------------------
% 0.20/0.54  % (13738)------------------------------
% 0.20/0.54  % (13739)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (13744)Refutation not found, incomplete strategy% (13744)------------------------------
% 0.20/0.54  % (13744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13744)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13744)Memory used [KB]: 10618
% 0.20/0.54  % (13744)Time elapsed: 0.147 s
% 0.20/0.54  % (13744)------------------------------
% 0.20/0.54  % (13744)------------------------------
% 0.20/0.55  % (13751)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (13741)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (13736)Refutation not found, incomplete strategy% (13736)------------------------------
% 0.20/0.56  % (13736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13736)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13736)Memory used [KB]: 10746
% 0.20/0.56  % (13736)Time elapsed: 0.142 s
% 0.20/0.56  % (13736)------------------------------
% 0.20/0.56  % (13736)------------------------------
% 0.20/0.56  % (13756)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (13753)Refutation not found, incomplete strategy% (13753)------------------------------
% 0.20/0.56  % (13753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13732)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (13735)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (13753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13753)Memory used [KB]: 10874
% 0.20/0.56  % (13753)Time elapsed: 0.150 s
% 0.20/0.56  % (13753)------------------------------
% 0.20/0.56  % (13753)------------------------------
% 0.20/0.57  % (13748)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.58  % (13735)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % (13740)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f388,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(subsumption_resolution,[],[f387,f81])).
% 0.20/0.59  fof(f81,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.20/0.59    inference(forward_demodulation,[],[f80,f52])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))),
% 0.20/0.59    inference(backward_demodulation,[],[f78,f79])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))) )),
% 0.20/0.59    inference(backward_demodulation,[],[f75,f76])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    ( ! [X1] : (k9_subset_1(k2_struct_0(sK0),X1,sK1) = k1_setfam_1(k2_tarski(X1,sK1))) )),
% 0.20/0.59    inference(resolution,[],[f72,f66])).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f57,f53])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.59    inference(backward_demodulation,[],[f40,f71])).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.59    inference(resolution,[],[f70,f47])).
% 0.20/0.59  fof(f47,plain,(
% 0.20/0.59    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,axiom,(
% 0.20/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    l1_struct_0(sK0)),
% 0.20/0.59    inference(resolution,[],[f39,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    l1_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30,f29,f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,negated_conjecture,(
% 0.20/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.59    inference(negated_conjecture,[],[f15])).
% 0.20/0.59  fof(f15,conjecture,(
% 0.20/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f75,plain,(
% 0.20/0.59    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)) )),
% 0.20/0.59    inference(resolution,[],[f72,f58])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.59  fof(f78,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK1,sK2))),
% 0.20/0.59    inference(backward_demodulation,[],[f74,f75])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.20/0.59    inference(backward_demodulation,[],[f44,f71])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f387,plain,(
% 0.20/0.59    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.20/0.59    inference(forward_demodulation,[],[f386,f296])).
% 0.20/0.59  fof(f296,plain,(
% 0.20/0.59    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))),
% 0.20/0.59    inference(forward_demodulation,[],[f295,f46])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.59  fof(f295,plain,(
% 0.20/0.59    k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.20/0.59    inference(superposition,[],[f65,f244])).
% 0.20/0.59  fof(f244,plain,(
% 0.20/0.59    k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))),
% 0.20/0.59    inference(backward_demodulation,[],[f199,f224])).
% 0.20/0.59  fof(f224,plain,(
% 0.20/0.59    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))),
% 0.20/0.59    inference(resolution,[],[f219,f113])).
% 0.20/0.59  fof(f113,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.59  fof(f112,plain,(
% 0.20/0.59    ( ! [X1] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = X1 | r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1) | r2_hidden(sK3(sK1,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK1,k2_struct_0(sK0)) = X1) )),
% 0.20/0.59    inference(resolution,[],[f92,f62])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.59    inference(rectify,[],[f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.59    inference(flattening,[],[f33])).
% 0.20/0.59  fof(f33,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.59    inference(nnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r2_hidden(sK3(X2,k2_struct_0(sK0),X3),sK1) | k4_xboole_0(X2,k2_struct_0(sK0)) = X3 | r2_hidden(sK3(X2,k2_struct_0(sK0),X3),X3)) )),
% 0.20/0.59    inference(resolution,[],[f77,f63])).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f77,plain,(
% 0.20/0.59    ( ! [X2] : (r2_hidden(X2,k2_struct_0(sK0)) | ~r2_hidden(X2,sK1)) )),
% 0.20/0.59    inference(resolution,[],[f72,f55])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.59  fof(f219,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(superposition,[],[f201,f46])).
% 0.20/0.59  fof(f201,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0))) )),
% 0.20/0.59    inference(superposition,[],[f177,f163])).
% 0.20/0.59  fof(f163,plain,(
% 0.20/0.59    ( ! [X0] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f155])).
% 0.20/0.59  fof(f155,plain,(
% 0.20/0.59    ( ! [X0] : (k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0) | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X0,X0)) )),
% 0.20/0.59    inference(resolution,[],[f126,f125])).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    ( ! [X2,X1] : (r2_hidden(sK3(sK1,k2_struct_0(sK0),k4_xboole_0(X1,X2)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(sK1,k2_struct_0(sK0))) )),
% 0.20/0.59    inference(resolution,[],[f113,f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f59])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ( ! [X4,X3] : (~r2_hidden(sK3(sK1,k2_struct_0(sK0),k4_xboole_0(X3,X4)),X4) | k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(X3,X4)) )),
% 0.20/0.59    inference(resolution,[],[f113,f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f60])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f37])).
% 0.20/0.59  fof(f177,plain,(
% 0.20/0.59    ( ! [X5] : (~r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f174,f173])).
% 0.20/0.59  fof(f173,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(sK1,k2_struct_0(sK0))) | r2_hidden(X3,X2)) )),
% 0.20/0.59    inference(superposition,[],[f69,f163])).
% 0.20/0.59  fof(f174,plain,(
% 0.20/0.59    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(sK1,k2_struct_0(sK0))) | ~r2_hidden(X5,X4)) )),
% 0.20/0.59    inference(superposition,[],[f68,f163])).
% 0.20/0.59  fof(f199,plain,(
% 0.20/0.59    k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(sK2,k2_struct_0(sK0))),
% 0.20/0.59    inference(resolution,[],[f177,f119])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    ( ! [X1] : (r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK2,k2_struct_0(sK0)) = X1) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.59  fof(f118,plain,(
% 0.20/0.59    ( ! [X1] : (k4_xboole_0(sK2,k2_struct_0(sK0)) = X1 | r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1) | r2_hidden(sK3(sK2,k2_struct_0(sK0),X1),X1) | k4_xboole_0(sK2,k2_struct_0(sK0)) = X1) )),
% 0.20/0.59    inference(resolution,[],[f94,f62])).
% 0.20/0.59  fof(f94,plain,(
% 0.20/0.59    ( ! [X2,X3] : (~r2_hidden(sK3(X2,k2_struct_0(sK0),X3),sK2) | k4_xboole_0(X2,k2_struct_0(sK0)) = X3 | r2_hidden(sK3(X2,k2_struct_0(sK0),X3),X3)) )),
% 0.20/0.59    inference(resolution,[],[f84,f63])).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    ( ! [X2] : (r2_hidden(X2,k2_struct_0(sK0)) | ~r2_hidden(X2,sK2)) )),
% 0.20/0.59    inference(resolution,[],[f73,f55])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.59    inference(backward_demodulation,[],[f42,f71])).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f54,f53])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.59  fof(f386,plain,(
% 0.20/0.59    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 0.20/0.59    inference(forward_demodulation,[],[f384,f101])).
% 0.20/0.59  fof(f101,plain,(
% 0.20/0.59    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.59    inference(subsumption_resolution,[],[f99,f41])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    v1_tops_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    ~v1_tops_1(sK1,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.59    inference(resolution,[],[f90,f72])).
% 0.20/0.59  fof(f90,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f87,f39])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X2,sK0) | k2_pre_topc(sK0,X2) = k2_struct_0(sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.59    inference(superposition,[],[f49,f71])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f32])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(nnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.59  fof(f384,plain,(
% 0.20/0.59    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,sK1))))),
% 0.20/0.59    inference(resolution,[],[f194,f72])).
% 0.20/0.59  fof(f194,plain,(
% 0.20/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_pre_topc(sK0,X1))))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f193,f52])).
% 0.20/0.59  fof(f193,plain,(
% 0.20/0.59    ( ! [X1] : (k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,X1),sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f192,f85])).
% 0.20/0.59  fof(f85,plain,(
% 0.20/0.59    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 0.20/0.59    inference(backward_demodulation,[],[f82,f83])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    ( ! [X1] : (k9_subset_1(k2_struct_0(sK0),X1,sK2) = k1_setfam_1(k2_tarski(X1,sK2))) )),
% 0.20/0.59    inference(resolution,[],[f73,f66])).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)) )),
% 0.20/0.59    inference(resolution,[],[f73,f58])).
% 0.20/0.59  fof(f192,plain,(
% 0.20/0.59    ( ! [X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(X1,sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(forward_demodulation,[],[f191,f85])).
% 0.20/0.59  fof(f191,plain,(
% 0.20/0.59    ( ! [X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f179,f43])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    v3_pre_topc(sK2,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f179,plain,(
% 0.20/0.59    ( ! [X1] : (~v3_pre_topc(sK2,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(resolution,[],[f89,f73])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f88,f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    v2_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f31])).
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f86,f39])).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.20/0.59    inference(superposition,[],[f51,f71])).
% 0.20/0.59  fof(f51,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (13735)------------------------------
% 0.20/0.59  % (13735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (13735)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (13735)Memory used [KB]: 10874
% 0.20/0.59  % (13735)Time elapsed: 0.178 s
% 0.20/0.59  % (13735)------------------------------
% 0.20/0.59  % (13735)------------------------------
% 0.20/0.59  % (13722)Success in time 0.241 s
%------------------------------------------------------------------------------
