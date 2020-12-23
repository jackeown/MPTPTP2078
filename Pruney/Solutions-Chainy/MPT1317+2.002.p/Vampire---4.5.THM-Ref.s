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
% DateTime   : Thu Dec  3 13:13:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 413 expanded)
%              Number of leaves         :   13 ( 169 expanded)
%              Depth                    :   15
%              Number of atoms          :  323 (2847 expanded)
%              Number of equality atoms :   26 ( 410 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(subsumption_resolution,[],[f283,f75])).

fof(f75,plain,(
    r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f74,f65])).

fof(f65,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tops_2(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & v2_tops_2(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v2_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v2_tops_2(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v2_tops_2(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
        & v2_tops_2(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & v2_tops_2(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v2_tops_2(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

fof(f63,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f54,plain,(
    ~ v2_tops_2(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f36])).

fof(f37,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f283,plain,(
    ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f280,f210])).

fof(f210,plain,(
    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f186,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f186,plain,(
    r1_tarski(sK4(sK2,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f127,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f127,plain,(
    r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f89,f75])).

fof(f89,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f280,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f169,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f66,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f165,f73])).

fof(f73,plain,(
    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f72,f65])).

fof(f72,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f69,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f165,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v4_pre_topc(sK4(sK2,sK1),sK0)
    | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f64,f77])).

fof(f77,plain,(
    ~ v4_pre_topc(sK4(sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f76,f65])).

fof(f76,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f71,f55])).

fof(f71,plain,
    ( ~ v4_pre_topc(sK4(sK2,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9737)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (9738)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (9737)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f284,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f283,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    r2_hidden(sK4(sK2,sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f74,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    l1_pre_topc(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f63,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    (((~v2_tops_2(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & v2_tops_2(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v2_tops_2(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & v2_tops_2(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ? [X3] : (~v2_tops_2(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v2_tops_2(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v2_tops_2(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v2_tops_2(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v2_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v2_tops_2(X3,X2)))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.47    inference(resolution,[],[f33,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    m1_pre_topc(sK2,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    r2_hidden(sK4(sK2,sK1),sK1) | ~l1_pre_topc(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f70,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.47    inference(forward_demodulation,[],[f35,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    sK1 = sK3),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    r2_hidden(sK4(sK2,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2)),
% 0.22/0.47    inference(resolution,[],[f54,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v2_tops_2(X1,X0) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(rectify,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ~v2_tops_2(sK1,sK2)),
% 0.22/0.47    inference(backward_demodulation,[],[f37,f36])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ~v2_tops_2(sK3,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f283,plain,(
% 0.22/0.47    ~r2_hidden(sK4(sK2,sK1),sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f280,f210])).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(resolution,[],[f186,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.47    inference(nnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    r1_tarski(sK4(sK2,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f127,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(equality_resolution,[],[f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(resolution,[],[f89,f75])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(resolution,[],[f32,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK2,sK1),sK1)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f275])).
% 0.22/0.48  fof(f275,plain,(
% 0.22/0.48    ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(sK2,sK1),sK1) | ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(resolution,[],[f169,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f67,f31])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f66,f32])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (v4_pre_topc(X0,sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f34,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v2_tops_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ~v4_pre_topc(sK4(sK2,sK1),sK0) | ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f165,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f65])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f69,f55])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2)),
% 0.22/0.48    inference(resolution,[],[f54,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_tops_2(X1,X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(sK4(sK2,sK1),sK0) | ~m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(resolution,[],[f64,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~v4_pre_topc(sK4(sK2,sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f76,f65])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~v4_pre_topc(sK4(sK2,sK1),sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f71,f55])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~v4_pre_topc(sK4(sK2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2)),
% 0.22/0.48    inference(resolution,[],[f54,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_tops_2(X1,X0) | ~v4_pre_topc(sK4(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0] : (v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f31])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0] : (v4_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f33,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X0,X3] : (v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (9737)------------------------------
% 0.22/0.48  % (9737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9737)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (9737)Memory used [KB]: 1791
% 0.22/0.48  % (9737)Time elapsed: 0.037 s
% 0.22/0.48  % (9737)------------------------------
% 0.22/0.48  % (9737)------------------------------
% 0.22/0.48  % (9729)Success in time 0.116 s
%------------------------------------------------------------------------------
