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
% DateTime   : Thu Dec  3 13:14:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  148 (3333 expanded)
%              Number of leaves         :   17 (1061 expanded)
%              Depth                    :   36
%              Number of atoms          :  538 (18993 expanded)
%              Number of equality atoms :   48 ( 555 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f583,plain,(
    $false ),
    inference(subsumption_resolution,[],[f582,f80])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f47,f78])).

fof(f78,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v2_compts_1(sK2,sK0)
    & v4_pre_topc(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v2_compts_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK0)
              & v4_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(X2,sK0)
            & v4_pre_topc(X2,sK0)
            & r1_tarski(X2,X1)
            & v2_compts_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(X2,sK0)
          & v4_pre_topc(X2,sK0)
          & r1_tarski(X2,sK1)
          & v2_compts_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(X2,sK0)
        & v4_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & v2_compts_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_compts_1(sK2,sK0)
      & v4_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & v2_compts_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f582,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f581,f78])).

fof(f581,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f580,f79])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f46,f78])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f580,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f579,f45])).

fof(f579,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f578,f51])).

fof(f51,plain,(
    ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f578,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f571,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f88,f78])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) ) ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f571,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f570,f49])).

fof(f49,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f570,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,sK1)
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f569,f116])).

fof(f116,plain,(
    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f99,f113])).

fof(f113,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f106,f78])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f99,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f96,f52])).

fof(f96,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f92,f53])).

fof(f92,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f91,f79])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k1_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k1_pre_topc(sK0,X0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f89,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f569,plain,(
    ! [X0] :
      ( v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f568,f514])).

fof(f514,plain,(
    v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f513,f205])).

fof(f205,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f204,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f204,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f202,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(forward_demodulation,[],[f200,f133])).

fof(f133,plain,(
    sK2 = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)) ),
    inference(resolution,[],[f132,f49])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0)) = X0 ) ),
    inference(resolution,[],[f117,f70])).

fof(f117,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1 ) ),
    inference(backward_demodulation,[],[f111,f116])).

fof(f111,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK0,sK1))))
      | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1 ) ),
    inference(forward_demodulation,[],[f107,f99])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1 ) ),
    inference(resolution,[],[f62,f92])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),sK2)))) ) ),
    inference(resolution,[],[f141,f49])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0)))) ) ),
    inference(forward_demodulation,[],[f140,f113])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ) ),
    inference(subsumption_resolution,[],[f138,f92])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f137,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f118,f70])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f100,f116])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK0,sK1))))
      | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f95,f99])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f92,f65])).

fof(f513,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f506,f236])).

fof(f236,plain,(
    v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f235,f205])).

fof(f235,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f232,f113])).

fof(f232,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f198,f79])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))
      | v4_pre_topc(sK2,k1_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f195,f89])).

fof(f195,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v4_pre_topc(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f194,f45])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f57])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f506,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f505,f113])).

fof(f505,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ) ),
    inference(subsumption_resolution,[],[f504,f92])).

fof(f504,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f503,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

fof(f503,plain,(
    v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f123,f502])).

fof(f502,plain,(
    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f501,f73])).

fof(f501,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f494,f70])).

fof(f494,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f493,f113])).

fof(f493,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f492,f79])).

fof(f492,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f489,f73])).

fof(f489,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f199,f116])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,X0)))
      | v2_compts_1(sK1,k1_pre_topc(sK0,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f197,f89])).

fof(f197,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK1,X0)
      | ~ r1_tarski(sK1,k2_struct_0(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f196,f45])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK1,X0)
      | ~ r1_tarski(sK1,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_compts_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X4,X1)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK3(X1,X2),X1)
                    & sK3(X1,X2) = X2
                    & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK3(X1,X2),X1)
        & sK3(X1,X2) = X2
        & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f123,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f122,f92])).

fof(f122,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f55,f116])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(f568,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f61,f567])).

fof(f567,plain,(
    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f565,f51])).

fof(f565,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f561,f49])).

fof(f561,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK3(k1_pre_topc(sK0,sK1),X0) = X0
      | v2_compts_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f560,f221])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f218,f70])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f215,f113])).

fof(f215,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f128,f79])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f127,f78])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1))))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f57,f89])).

fof(f560,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK3(k1_pre_topc(sK0,sK1),X0) = X0
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f556,f116])).

fof(f556,plain,(
    ! [X0] :
      ( sK3(k1_pre_topc(sK0,sK1),X0) = X0
      | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1)))
      | v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f259,f79])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK3(k1_pre_topc(sK0,X0),X1) = X1
      | ~ r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0)))
      | v2_compts_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f258,f78])).

fof(f258,plain,(
    ! [X0,X1] :
      ( sK3(k1_pre_topc(sK0,X0),X1) = X1
      | ~ r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_compts_1(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f254,f45])).

fof(f254,plain,(
    ! [X0,X1] :
      ( sK3(k1_pre_topc(sK0,X0),X1) = X1
      | ~ r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_compts_1(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f60,f89])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sK3(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK3(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (19099)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (19107)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.46  % (19099)Refutation not found, incomplete strategy% (19099)------------------------------
% 0.20/0.46  % (19099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (19099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (19099)Memory used [KB]: 6140
% 0.20/0.46  % (19099)Time elapsed: 0.057 s
% 0.20/0.46  % (19099)------------------------------
% 0.20/0.46  % (19099)------------------------------
% 0.20/0.49  % (19086)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (19088)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (19089)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (19093)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (19101)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (19087)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (19100)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (19086)Refutation not found, incomplete strategy% (19086)------------------------------
% 0.20/0.51  % (19086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19086)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19086)Memory used [KB]: 10618
% 0.20/0.51  % (19086)Time elapsed: 0.091 s
% 0.20/0.51  % (19086)------------------------------
% 0.20/0.51  % (19086)------------------------------
% 0.20/0.51  % (19090)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (19091)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (19095)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (19108)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (19106)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (19103)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (19110)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (19105)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (19102)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (19092)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (19097)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (19092)Refutation not found, incomplete strategy% (19092)------------------------------
% 0.20/0.53  % (19092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19092)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19092)Memory used [KB]: 10618
% 0.20/0.53  % (19092)Time elapsed: 0.104 s
% 0.20/0.53  % (19092)------------------------------
% 0.20/0.53  % (19092)------------------------------
% 0.20/0.53  % (19097)Refutation not found, incomplete strategy% (19097)------------------------------
% 0.20/0.53  % (19097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19097)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19097)Memory used [KB]: 10618
% 0.20/0.53  % (19097)Time elapsed: 0.129 s
% 0.20/0.53  % (19097)------------------------------
% 0.20/0.53  % (19097)------------------------------
% 0.20/0.53  % (19096)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (19111)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (19091)Refutation not found, incomplete strategy% (19091)------------------------------
% 0.20/0.53  % (19091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19091)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19091)Memory used [KB]: 6140
% 0.20/0.53  % (19091)Time elapsed: 0.104 s
% 0.20/0.53  % (19091)------------------------------
% 0.20/0.53  % (19091)------------------------------
% 0.20/0.54  % (19104)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (19109)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (19098)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.55  % (19094)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.55  % (19089)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f583,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f582,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(backward_demodulation,[],[f47,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f52,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    l1_struct_0(sK0)),
% 0.20/0.55    inference(resolution,[],[f53,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    l1_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ((~v2_compts_1(sK2,sK0) & v4_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,X1) & v2_compts_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ? [X1] : (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,X1) & v2_compts_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ? [X2] : (~v2_compts_1(X2,sK0) & v4_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_compts_1(sK2,sK0) & v4_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & v2_compts_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.55  fof(f14,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.55    inference(negated_conjecture,[],[f13])).
% 0.20/0.55  fof(f13,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f582,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(forward_demodulation,[],[f581,f78])).
% 0.20/0.55  fof(f581,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f580,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(backward_demodulation,[],[f46,f78])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f580,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f579,f45])).
% 0.20/0.55  fof(f579,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f578,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ~v2_compts_1(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f578,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(resolution,[],[f571,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X0] : (m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f88,f78])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X0),sK0)) )),
% 0.20/0.55    inference(resolution,[],[f65,f45])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.55  fof(f571,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f570,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    r1_tarski(sK2,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f570,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK2,sK1) | v2_compts_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f569,f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(backward_demodulation,[],[f99,f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f110,f79])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) )),
% 0.20/0.55    inference(forward_demodulation,[],[f106,f78])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) )),
% 0.20/0.55    inference(resolution,[],[f62,f45])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f96,f52])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f92,f53])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f91,f79])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k1_pre_topc(sK0,X0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f90,f45])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k1_pre_topc(sK0,X0)) | ~l1_pre_topc(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f89,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.55  fof(f569,plain,(
% 0.20/0.55    ( ! [X0] : (v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f568,f514])).
% 0.20/0.55  fof(f514,plain,(
% 0.20/0.55    v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f513,f205])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.20/0.55    inference(resolution,[],[f204,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK2) | m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.20/0.55    inference(resolution,[],[f202,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK2)) | m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f200,f133])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    sK2 = u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),sK2))),
% 0.20/0.55    inference(resolution,[],[f132,f49])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0)) = X0) )),
% 0.20/0.55    inference(resolution,[],[f117,f70])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1) )),
% 0.20/0.55    inference(backward_demodulation,[],[f111,f116])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK0,sK1)))) | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1) )),
% 0.20/0.55    inference(forward_demodulation,[],[f107,f99])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X1)) = X1) )),
% 0.20/0.55    inference(resolution,[],[f62,f92])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),sK2))))) )),
% 0.20/0.55    inference(resolution,[],[f141,f49])).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0))))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f140,f113])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0)))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f138,f92])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(k1_pre_topc(sK0,sK1),X0)))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f137,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X0] : (m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.55    inference(resolution,[],[f118,f70])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f100,f116])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k1_pre_topc(sK0,sK1)))) | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f95,f99])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | m1_pre_topc(k1_pre_topc(k1_pre_topc(sK0,sK1),X0),k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f92,f65])).
% 0.20/0.55  fof(f513,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f506,f236])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f235,f205])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(forward_demodulation,[],[f232,f113])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f198,f79])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) | v4_pre_topc(sK2,k1_pre_topc(sK0,X0))) )),
% 0.20/0.55    inference(resolution,[],[f195,f89])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v4_pre_topc(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f194,f45])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK2,X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f76,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    v4_pre_topc(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X3] : (~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f72,f57])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.20/0.55  fof(f506,plain,(
% 0.20/0.55    ( ! [X0] : (~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f505,f113])).
% 0.20/0.55  fof(f505,plain,(
% 0.20/0.55    ( ! [X0] : (~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f504,f92])).
% 0.20/0.55  fof(f504,plain,(
% 0.20/0.55    ( ! [X0] : (~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f503,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_compts_1(X0) | ~v4_pre_topc(X1,X0) | v2_compts_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).
% 0.20/0.55  fof(f503,plain,(
% 0.20/0.55    v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f123,f502])).
% 0.20/0.55  fof(f502,plain,(
% 0.20/0.55    v2_compts_1(sK1,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f501,f73])).
% 0.20/0.55  fof(f501,plain,(
% 0.20/0.55    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 0.20/0.55    inference(resolution,[],[f494,f70])).
% 0.20/0.55  fof(f494,plain,(
% 0.20/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_compts_1(sK1,k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(forward_demodulation,[],[f493,f113])).
% 0.20/0.55  fof(f493,plain,(
% 0.20/0.55    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))),
% 0.20/0.55    inference(subsumption_resolution,[],[f492,f79])).
% 0.20/0.55  fof(f492,plain,(
% 0.20/0.55    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f489,f73])).
% 0.20/0.55  fof(f489,plain,(
% 0.20/0.55    ~r1_tarski(sK1,sK1) | v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(superposition,[],[f199,f116])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,X0))) | v2_compts_1(sK1,k1_pre_topc(sK0,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X0)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f197,f89])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_compts_1(sK1,X0) | ~r1_tarski(sK1,k2_struct_0(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f196,f45])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0) | ~r1_tarski(sK1,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.55    inference(resolution,[],[f75,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    v2_compts_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (~v2_compts_1(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X4,X1) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f71,f57])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK3(X1,X2),X1) & sK3(X1,X2) = X2 & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK3(X1,X2),X1) & sK3(X1,X2) = X2 & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(rectify,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(subsumption_resolution,[],[f122,f92])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.20/0.55    inference(superposition,[],[f55,f116])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).
% 0.20/0.55  fof(f568,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(superposition,[],[f61,f567])).
% 0.20/0.55  fof(f567,plain,(
% 0.20/0.55    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f565,f51])).
% 0.20/0.55  fof(f565,plain,(
% 0.20/0.55    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | v2_compts_1(sK2,sK0)),
% 0.20/0.55    inference(resolution,[],[f561,f49])).
% 0.20/0.55  fof(f561,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | sK3(k1_pre_topc(sK0,sK1),X0) = X0 | v2_compts_1(X0,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f560,f221])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f218,f70])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f215,f113])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f128,f79])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f127,f78])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f126,f45])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X1)))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f57,f89])).
% 0.20/0.55  fof(f560,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | sK3(k1_pre_topc(sK0,sK1),X0) = X0 | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f556,f116])).
% 0.20/0.55  fof(f556,plain,(
% 0.20/0.55    ( ! [X0] : (sK3(k1_pre_topc(sK0,sK1),X0) = X0 | ~r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1))) | v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f259,f79])).
% 0.20/0.55  fof(f259,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK3(k1_pre_topc(sK0,X0),X1) = X1 | ~r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0))) | v2_compts_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f258,f78])).
% 0.20/0.55  fof(f258,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(k1_pre_topc(sK0,X0),X1) = X1 | ~r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f254,f45])).
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK3(k1_pre_topc(sK0,X0),X1) = X1 | ~r1_tarski(X1,k2_struct_0(k1_pre_topc(sK0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f60,f89])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | sK3(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v2_compts_1(sK3(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (19089)------------------------------
% 0.20/0.55  % (19089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19089)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (19089)Memory used [KB]: 6652
% 0.20/0.55  % (19089)Time elapsed: 0.147 s
% 0.20/0.55  % (19089)------------------------------
% 0.20/0.55  % (19089)------------------------------
% 0.20/0.55  % (19085)Success in time 0.198 s
%------------------------------------------------------------------------------
