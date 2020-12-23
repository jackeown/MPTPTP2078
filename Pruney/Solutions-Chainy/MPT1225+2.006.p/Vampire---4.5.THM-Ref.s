%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 396 expanded)
%              Number of leaves         :    9 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  192 (2256 expanded)
%              Number of equality atoms :   26 ( 396 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
            & v4_pre_topc(X2,sK0)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
          & v4_pre_topc(X2,sK0)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
        & v4_pre_topc(X2,sK0)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
      & v4_pre_topc(sK2,sK0)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).

fof(f75,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f74,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(subsumption_resolution,[],[f73,f59])).

fof(f59,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f54,f57])).

fof(f57,plain,(
    sK2 = k2_pre_topc(sK0,sK2) ),
    inference(subsumption_resolution,[],[f42,f56])).

fof(f56,plain,(
    r1_tarski(k2_pre_topc(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f55,f23])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK2),sK2) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f48,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X1),sK2) ) ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f42,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | sK2 = k2_pre_topc(sK0,sK2) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f37,f23])).

fof(f54,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    inference(backward_demodulation,[],[f26,f51])).

fof(f51,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f41,f50])).

fof(f50,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f49,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f45,f22])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),sK1) ) ),
    inference(resolution,[],[f44,f24])).

fof(f24,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f38,f32])).

fof(f38,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f37,f22])).

fof(f26,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(resolution,[],[f71,f32])).

fof(f71,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f69,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f65,f57])).

fof(f65,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f62,f51])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f61,f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (22491)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (22494)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (22493)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (22493)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (22510)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (22503)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (22495)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (22499)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (22508)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (22502)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (22511)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (22500)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f75,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ((k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X2] : (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_1)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f74,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,X1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(resolution,[],[f37,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 0.22/0.51    inference(resolution,[],[f27,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f73,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f54,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    sK2 = k2_pre_topc(sK0,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f42,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    r1_tarski(k2_pre_topc(sK0,sK2),sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f55,f23])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK2),sK2)),
% 0.22/0.51    inference(resolution,[],[f48,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X1),sK2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f46,f23])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X1] : (~r1_tarski(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X1),sK2)) )),
% 0.22/0.51    inference(resolution,[],[f44,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    v4_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v4_pre_topc(X1,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),X1)) )),
% 0.22/0.51    inference(resolution,[],[f29,f21])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~r1_tarski(k2_pre_topc(sK0,sK2),sK2) | sK2 = k2_pre_topc(sK0,sK2)),
% 0.22/0.51    inference(resolution,[],[f39,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f37,f23])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f26,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f41,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f49,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.51    inference(resolution,[],[f47,f34])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f45,f22])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f44,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    v4_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f38,f32])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f37,f22])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.22/0.51    inference(resolution,[],[f71,f32])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f23])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(superposition,[],[f65,f57])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f62,f51])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)))) )),
% 0.22/0.51    inference(resolution,[],[f61,f22])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)))) )),
% 0.22/0.51    inference(resolution,[],[f28,f21])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22493)------------------------------
% 0.22/0.51  % (22493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22493)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22493)Memory used [KB]: 6140
% 0.22/0.51  % (22493)Time elapsed: 0.083 s
% 0.22/0.51  % (22493)------------------------------
% 0.22/0.51  % (22493)------------------------------
% 0.22/0.52  % (22515)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (22489)Success in time 0.155 s
%------------------------------------------------------------------------------
