%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1373+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (1858 expanded)
%              Number of leaves         :   11 ( 653 expanded)
%              Depth                    :   23
%              Number of atoms          :  340 (14293 expanded)
%              Number of equality atoms :   42 (1916 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(global_subsumption,[],[f29,f56,f58,f122,f137])).

fof(f137,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK1) ),
    inference(superposition,[],[f120,f55])).

fof(f55,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f54,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f51,f29])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ v2_compts_1(sK3,sK1)
      | ~ v2_compts_1(sK2,sK0) )
    & ( v2_compts_1(sK3,sK1)
      | v2_compts_1(sK2,sK0) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK0) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK1)
                | ~ v2_compts_1(X2,sK0) )
              & ( v2_compts_1(X3,sK1)
                | v2_compts_1(X2,sK0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK1)
              | ~ v2_compts_1(X2,sK0) )
            & ( v2_compts_1(X3,sK1)
              | v2_compts_1(X2,sK0) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK1)
            | ~ v2_compts_1(sK2,sK0) )
          & ( v2_compts_1(X3,sK1)
            | v2_compts_1(sK2,sK0) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK1)
          | ~ v2_compts_1(sK2,sK0) )
        & ( v2_compts_1(X3,sK1)
          | v2_compts_1(sK2,sK0) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ~ v2_compts_1(sK3,sK1)
        | ~ v2_compts_1(sK2,sK0) )
      & ( v2_compts_1(sK3,sK1)
        | v2_compts_1(sK2,sK0) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f111,f119])).

fof(f119,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(global_subsumption,[],[f44,f117])).

fof(f117,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f85,f116])).

fof(f116,plain,(
    sK2 = sK4(sK1,sK2) ),
    inference(global_subsumption,[],[f45,f29,f56,f58,f66,f115])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK1)
    | sK2 = sK4(sK1,sK2) ),
    inference(superposition,[],[f113,f55])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(sK2,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | v2_compts_1(sK2,X1)
      | sK2 = sK4(sK1,sK2) ) ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,
    ( v2_compts_1(sK2,sK0)
    | sK2 = sK4(sK1,sK2) ),
    inference(global_subsumption,[],[f29,f65])).

fof(f65,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | sK2 = sK4(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f49])).

fof(f49,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f36,f28])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK4(X0,X1) = X1
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(X1,sK0) ) ),
    inference(forward_demodulation,[],[f59,f49])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = X1
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | sK4(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK4(X1,X2),X1)
                    & sK4(X1,X2) = X2
                    & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK4(X1,X2),X1)
        & sK4(X1,X2) = X2
        & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f45,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f34,f32])).

fof(f32,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,
    ( ~ v2_compts_1(sK4(sK1,sK2),sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(global_subsumption,[],[f29,f84])).

fof(f84,plain,
    ( ~ v2_compts_1(sK4(sK1,sK2),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f82,f58])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ v2_compts_1(sK4(X0,sK2),X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f80,f50])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_compts_1(sK4(X0,X1),X0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(X1,sK0) ) ),
    inference(forward_demodulation,[],[f78,f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(sK4(X0,X1),X0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(sK4(X1,X2),X1)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,
    ( v2_compts_1(sK2,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f33,f32])).

fof(f33,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK2,X0) ) ),
    inference(resolution,[],[f109,f50])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(X0,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | v2_compts_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f107,f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(X0,k2_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X1,sK0)
      | v2_compts_1(X0,X1) ) ),
    inference(resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_compts_1(X4,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f122,plain,(
    ~ v2_compts_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f45,f119])).

fof(f58,plain,(
    r1_tarski(sK2,k2_struct_0(sK1)) ),
    inference(resolution,[],[f42,f56])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f46,f55])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f31,f32])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f23])).

% (8437)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
