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
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 617 expanded)
%              Number of leaves         :   10 ( 247 expanded)
%              Depth                    :   27
%              Number of atoms          :  308 (4707 expanded)
%              Number of equality atoms :   51 (1266 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(subsumption_resolution,[],[f173,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v1_tops_2(sK3,sK1)
    & v1_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X1)
                    & v1_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X1)
                & v1_tops_2(X2,sK0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,sK1)
              & v1_tops_2(X2,sK0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_tops_2(X3,sK1)
            & v1_tops_2(X2,sK0)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X3] :
          ( ~ v1_tops_2(X3,sK1)
          & v1_tops_2(sK2,sK0)
          & sK2 = X3
          & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ~ v1_tops_2(X3,sK1)
        & v1_tops_2(sK2,sK0)
        & sK2 = X3
        & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
   => ( ~ v1_tops_2(sK3,sK1)
      & v1_tops_2(sK2,sK0)
      & sK2 = sK3
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X1)
                  & v1_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v1_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v1_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v1_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v1_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).

fof(f173,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f172,f61])).

fof(f61,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f57,f28])).

fof(f28,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X6,X4,X5] :
      ( ~ l1_pre_topc(X4)
      | u1_struct_0(X4) = X5
      | g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) != g1_pre_topc(X5,X6) ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f172,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f171,f25])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f169,f41])).

fof(f41,plain,(
    ~ v1_tops_2(sK2,sK1) ),
    inference(backward_demodulation,[],[f31,f29])).

fof(f29,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ~ v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f169,plain,
    ( v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f168,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f168,plain,(
    v3_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f167,f26])).

fof(f167,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f166,f41])).

fof(f166,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK1)
    | v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f164,f127])).

fof(f127,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f125,f25])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_2(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f36,f61])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK4(sK1,sK2),sK1) ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f96,f61])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f34,f86])).

fof(f86,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(superposition,[],[f77,f62])).

fof(f62,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f28,f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f71,f25])).

fof(f71,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f32,f61])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f163,plain,(
    r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f162,f41])).

fof(f162,plain,
    ( v1_tops_2(sK2,sK1)
    | r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f161,f26])).

fof(f161,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(sK2,sK1)
    | r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f129,f136])).

fof(f136,plain,(
    v3_pre_topc(sK4(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f135,f26])).

fof(f135,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f134,f41])).

% (22624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f134,plain,
    ( v3_pre_topc(sK4(sK1,sK2),sK0)
    | v1_tops_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f133,f127])).

fof(f133,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK4(sK1,sK2),sK0) ),
    inference(resolution,[],[f132,f120])).

fof(f120,plain,(
    r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | v1_tops_2(sK2,sK1) ),
    inference(resolution,[],[f110,f26])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(sK4(sK1,X1),X1)
      | v1_tops_2(X1,sK1) ) ),
    inference(forward_demodulation,[],[f109,f61])).

fof(f109,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | v1_tops_2(X1,sK1) ) ),
    inference(resolution,[],[f37,f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f131,f24])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f26])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_tops_2(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK4(sK1,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X0,sK1)
      | r2_hidden(sK4(sK1,X0),u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f128,f24])).

fof(f128,plain,(
    ! [X0] :
      ( v1_tops_2(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v3_pre_topc(sK4(sK1,X0),sK0)
      | r2_hidden(sK4(sK1,X0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f127,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (803766272)
% 0.14/0.37  ipcrm: permission denied for id (803799041)
% 0.14/0.37  ipcrm: permission denied for id (803831811)
% 0.14/0.37  ipcrm: permission denied for id (803897351)
% 0.14/0.38  ipcrm: permission denied for id (803930120)
% 0.14/0.38  ipcrm: permission denied for id (803962889)
% 0.14/0.38  ipcrm: permission denied for id (804028428)
% 0.14/0.39  ipcrm: permission denied for id (804126738)
% 0.14/0.39  ipcrm: permission denied for id (804159507)
% 0.14/0.39  ipcrm: permission denied for id (804192277)
% 0.14/0.40  ipcrm: permission denied for id (804290587)
% 0.14/0.40  ipcrm: permission denied for id (804323356)
% 0.14/0.40  ipcrm: permission denied for id (804421663)
% 0.22/0.41  ipcrm: permission denied for id (804519972)
% 0.22/0.41  ipcrm: permission denied for id (804552741)
% 0.22/0.41  ipcrm: permission denied for id (804585510)
% 0.22/0.42  ipcrm: permission denied for id (804651048)
% 0.22/0.42  ipcrm: permission denied for id (804683817)
% 0.22/0.42  ipcrm: permission denied for id (804814892)
% 0.22/0.42  ipcrm: permission denied for id (804782127)
% 0.22/0.43  ipcrm: permission denied for id (804880433)
% 0.22/0.43  ipcrm: permission denied for id (804913202)
% 0.22/0.43  ipcrm: permission denied for id (804945974)
% 0.22/0.44  ipcrm: permission denied for id (805011513)
% 0.22/0.44  ipcrm: permission denied for id (805044282)
% 0.22/0.44  ipcrm: permission denied for id (805077051)
% 0.22/0.44  ipcrm: permission denied for id (805109821)
% 0.22/0.46  ipcrm: permission denied for id (805437516)
% 0.22/0.47  ipcrm: permission denied for id (805535825)
% 0.22/0.47  ipcrm: permission denied for id (805601364)
% 0.22/0.47  ipcrm: permission denied for id (805634134)
% 0.22/0.47  ipcrm: permission denied for id (805666903)
% 0.22/0.48  ipcrm: permission denied for id (805732441)
% 0.22/0.49  ipcrm: permission denied for id (805830752)
% 0.22/0.49  ipcrm: permission denied for id (805929059)
% 0.22/0.50  ipcrm: permission denied for id (806027370)
% 0.22/0.50  ipcrm: permission denied for id (806125678)
% 0.22/0.50  ipcrm: permission denied for id (806158447)
% 0.22/0.51  ipcrm: permission denied for id (806256757)
% 0.22/0.52  ipcrm: permission denied for id (806453372)
% 0.22/0.52  ipcrm: permission denied for id (806518910)
% 1.21/0.69  % (22626)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.70  % (22626)Refutation found. Thanks to Tanya!
% 1.21/0.70  % SZS status Theorem for theBenchmark
% 1.21/0.70  % (22642)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.70  % (22623)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.70  % (22634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.71  % (22622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.61/0.71  % (22621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.72  % SZS output start Proof for theBenchmark
% 1.61/0.72  fof(f174,plain,(
% 1.61/0.72    $false),
% 1.61/0.72    inference(subsumption_resolution,[],[f173,f26])).
% 1.61/0.72  fof(f26,plain,(
% 1.61/0.72    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f18,plain,(
% 1.61/0.72    (((~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.61/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f17,f16,f15,f14])).
% 1.61/0.72  fof(f14,plain,(
% 1.61/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.61/0.72    introduced(choice_axiom,[])).
% 1.61/0.72  fof(f15,plain,(
% 1.61/0.72    ? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1))),
% 1.61/0.72    introduced(choice_axiom,[])).
% 1.61/0.72  fof(f16,plain,(
% 1.61/0.72    ? [X2] : (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.61/0.72    introduced(choice_axiom,[])).
% 1.61/0.72  fof(f17,plain,(
% 1.61/0.72    ? [X3] : (~v1_tops_2(X3,sK1) & v1_tops_2(sK2,sK0) & sK2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) => (~v1_tops_2(sK3,sK1) & v1_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),
% 1.61/0.72    introduced(choice_axiom,[])).
% 1.61/0.72  fof(f8,plain,(
% 1.61/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X1) & v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.61/0.72    inference(flattening,[],[f7])).
% 1.61/0.72  fof(f7,plain,(
% 1.61/0.72    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v1_tops_2(X3,X1) & (v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.61/0.72    inference(ennf_transformation,[],[f6])).
% 1.61/0.72  fof(f6,negated_conjecture,(
% 1.61/0.72    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 1.61/0.72    inference(negated_conjecture,[],[f5])).
% 1.61/0.72  fof(f5,conjecture,(
% 1.61/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v1_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v1_tops_2(X3,X1))))))),
% 1.61/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_waybel_9)).
% 1.61/0.72  fof(f173,plain,(
% 1.61/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(forward_demodulation,[],[f172,f61])).
% 1.61/0.72  fof(f61,plain,(
% 1.61/0.72    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.61/0.72    inference(trivial_inequality_removal,[],[f59])).
% 1.61/0.72  fof(f59,plain,(
% 1.61/0.72    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.61/0.72    inference(superposition,[],[f57,f28])).
% 1.61/0.72  fof(f28,plain,(
% 1.61/0.72    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f57,plain,(
% 1.61/0.72    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0) )),
% 1.61/0.72    inference(resolution,[],[f45,f24])).
% 1.61/0.72  fof(f24,plain,(
% 1.61/0.72    l1_pre_topc(sK0)),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f45,plain,(
% 1.61/0.72    ( ! [X6,X4,X5] : (~l1_pre_topc(X4) | u1_struct_0(X4) = X5 | g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) != g1_pre_topc(X5,X6)) )),
% 1.61/0.72    inference(resolution,[],[f39,f32])).
% 1.61/0.72  fof(f32,plain,(
% 1.61/0.72    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f9])).
% 1.61/0.72  fof(f9,plain,(
% 1.61/0.72    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(ennf_transformation,[],[f2])).
% 1.61/0.72  fof(f2,axiom,(
% 1.61/0.72    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.61/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.61/0.72  fof(f39,plain,(
% 1.61/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 1.61/0.72    inference(cnf_transformation,[],[f13])).
% 1.61/0.72  fof(f13,plain,(
% 1.61/0.72    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.61/0.72    inference(ennf_transformation,[],[f3])).
% 1.61/0.72  fof(f3,axiom,(
% 1.61/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.61/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.61/0.72  fof(f172,plain,(
% 1.61/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.61/0.72    inference(subsumption_resolution,[],[f171,f25])).
% 1.61/0.72  fof(f25,plain,(
% 1.61/0.72    l1_pre_topc(sK1)),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f171,plain,(
% 1.61/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)),
% 1.61/0.72    inference(subsumption_resolution,[],[f169,f41])).
% 1.61/0.72  fof(f41,plain,(
% 1.61/0.72    ~v1_tops_2(sK2,sK1)),
% 1.61/0.72    inference(backward_demodulation,[],[f31,f29])).
% 1.61/0.72  fof(f29,plain,(
% 1.61/0.72    sK2 = sK3),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f31,plain,(
% 1.61/0.72    ~v1_tops_2(sK3,sK1)),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f169,plain,(
% 1.61/0.72    v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)),
% 1.61/0.72    inference(resolution,[],[f168,f38])).
% 1.61/0.72  fof(f38,plain,(
% 1.61/0.72    ( ! [X0,X1] : (~v3_pre_topc(sK4(X0,X1),X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f23])).
% 1.61/0.72  fof(f23,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.61/0.72  fof(f22,plain,(
% 1.61/0.72    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.61/0.72    introduced(choice_axiom,[])).
% 1.61/0.72  fof(f21,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(rectify,[],[f20])).
% 1.61/0.72  fof(f20,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(nnf_transformation,[],[f12])).
% 1.61/0.72  fof(f12,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(flattening,[],[f11])).
% 1.61/0.72  fof(f11,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(ennf_transformation,[],[f4])).
% 1.61/0.72  fof(f4,axiom,(
% 1.61/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 1.61/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 1.61/0.72  fof(f168,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK1)),
% 1.61/0.72    inference(subsumption_resolution,[],[f167,f26])).
% 1.61/0.72  fof(f167,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(subsumption_resolution,[],[f166,f41])).
% 1.61/0.72  fof(f166,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK1) | v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(resolution,[],[f164,f127])).
% 1.61/0.72  fof(f127,plain,(
% 1.61/0.72    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 1.61/0.72    inference(subsumption_resolution,[],[f125,f25])).
% 1.61/0.72  fof(f125,plain,(
% 1.61/0.72    ( ! [X0] : (m1_subset_1(sK4(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1)) )),
% 1.61/0.72    inference(superposition,[],[f36,f61])).
% 1.61/0.72  fof(f36,plain,(
% 1.61/0.72    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f23])).
% 1.61/0.72  fof(f164,plain,(
% 1.61/0.72    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK1,sK2),sK1)),
% 1.61/0.72    inference(resolution,[],[f163,f97])).
% 1.61/0.72  fof(f97,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK1)) )),
% 1.61/0.72    inference(forward_demodulation,[],[f96,f61])).
% 1.61/0.72  fof(f96,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.61/0.72    inference(subsumption_resolution,[],[f94,f25])).
% 1.61/0.72  fof(f94,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 1.61/0.72    inference(superposition,[],[f34,f86])).
% 1.61/0.72  fof(f86,plain,(
% 1.61/0.72    u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 1.61/0.72    inference(equality_resolution,[],[f83])).
% 1.61/0.72  fof(f83,plain,(
% 1.61/0.72    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK1) = X1) )),
% 1.61/0.72    inference(superposition,[],[f77,f62])).
% 1.61/0.72  fof(f62,plain,(
% 1.61/0.72    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))),
% 1.61/0.72    inference(backward_demodulation,[],[f28,f61])).
% 1.61/0.72  fof(f77,plain,(
% 1.61/0.72    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) | u1_pre_topc(sK1) = X1) )),
% 1.61/0.72    inference(resolution,[],[f73,f40])).
% 1.61/0.72  fof(f40,plain,(
% 1.61/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 1.61/0.72    inference(cnf_transformation,[],[f13])).
% 1.61/0.72  fof(f73,plain,(
% 1.61/0.72    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(subsumption_resolution,[],[f71,f25])).
% 1.61/0.72  fof(f71,plain,(
% 1.61/0.72    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1)),
% 1.61/0.72    inference(superposition,[],[f32,f61])).
% 1.61/0.72  fof(f34,plain,(
% 1.61/0.72    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f19])).
% 1.61/0.72  fof(f19,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(nnf_transformation,[],[f10])).
% 1.61/0.72  fof(f10,plain,(
% 1.61/0.72    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.72    inference(ennf_transformation,[],[f1])).
% 1.61/0.72  fof(f1,axiom,(
% 1.61/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.61/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.61/0.72  fof(f163,plain,(
% 1.61/0.72    r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0))),
% 1.61/0.72    inference(subsumption_resolution,[],[f162,f41])).
% 1.61/0.72  fof(f162,plain,(
% 1.61/0.72    v1_tops_2(sK2,sK1) | r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0))),
% 1.61/0.72    inference(subsumption_resolution,[],[f161,f26])).
% 1.61/0.72  fof(f161,plain,(
% 1.61/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(sK2,sK1) | r2_hidden(sK4(sK1,sK2),u1_pre_topc(sK0))),
% 1.61/0.72    inference(resolution,[],[f129,f136])).
% 1.61/0.72  fof(f136,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK0)),
% 1.61/0.72    inference(subsumption_resolution,[],[f135,f26])).
% 1.61/0.72  fof(f135,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(subsumption_resolution,[],[f134,f41])).
% 1.61/0.72  % (22624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.72  fof(f134,plain,(
% 1.61/0.72    v3_pre_topc(sK4(sK1,sK2),sK0) | v1_tops_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.72    inference(resolution,[],[f133,f127])).
% 1.61/0.72  fof(f133,plain,(
% 1.61/0.72    ~m1_subset_1(sK4(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK4(sK1,sK2),sK0)),
% 1.61/0.72    inference(resolution,[],[f132,f120])).
% 1.61/0.72  fof(f120,plain,(
% 1.61/0.72    r2_hidden(sK4(sK1,sK2),sK2)),
% 1.61/0.72    inference(subsumption_resolution,[],[f117,f41])).
% 1.61/0.72  fof(f117,plain,(
% 1.61/0.72    r2_hidden(sK4(sK1,sK2),sK2) | v1_tops_2(sK2,sK1)),
% 1.61/0.72    inference(resolution,[],[f110,f26])).
% 1.61/0.72  fof(f110,plain,(
% 1.61/0.72    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK4(sK1,X1),X1) | v1_tops_2(X1,sK1)) )),
% 1.61/0.72    inference(forward_demodulation,[],[f109,f61])).
% 1.61/0.72  fof(f109,plain,(
% 1.61/0.72    ( ! [X1] : (r2_hidden(sK4(sK1,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v1_tops_2(X1,sK1)) )),
% 1.61/0.72    inference(resolution,[],[f37,f25])).
% 1.61/0.72  fof(f37,plain,(
% 1.61/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f23])).
% 1.61/0.72  fof(f132,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 1.61/0.72    inference(subsumption_resolution,[],[f131,f24])).
% 1.61/0.72  fof(f131,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 1.61/0.72    inference(subsumption_resolution,[],[f130,f26])).
% 1.61/0.72  fof(f130,plain,(
% 1.61/0.72    ( ! [X0] : (~r2_hidden(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) )),
% 1.61/0.72    inference(resolution,[],[f35,f30])).
% 1.61/0.72  fof(f30,plain,(
% 1.61/0.72    v1_tops_2(sK2,sK0)),
% 1.61/0.72    inference(cnf_transformation,[],[f18])).
% 1.61/0.72  fof(f35,plain,(
% 1.61/0.72    ( ! [X0,X3,X1] : (~v1_tops_2(X1,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f23])).
% 1.61/0.72  fof(f129,plain,(
% 1.61/0.72    ( ! [X0] : (~v3_pre_topc(sK4(sK1,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK1) | r2_hidden(sK4(sK1,X0),u1_pre_topc(sK0))) )),
% 1.61/0.72    inference(subsumption_resolution,[],[f128,f24])).
% 1.61/0.72  fof(f128,plain,(
% 1.61/0.72    ( ! [X0] : (v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v3_pre_topc(sK4(sK1,X0),sK0) | r2_hidden(sK4(sK1,X0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)) )),
% 1.61/0.72    inference(resolution,[],[f127,f33])).
% 1.61/0.72  fof(f33,plain,(
% 1.61/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.61/0.72    inference(cnf_transformation,[],[f19])).
% 1.61/0.72  % SZS output end Proof for theBenchmark
% 1.61/0.72  % (22626)------------------------------
% 1.61/0.72  % (22626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.72  % (22626)Termination reason: Refutation
% 1.61/0.72  
% 1.61/0.72  % (22626)Memory used [KB]: 6268
% 1.61/0.72  % (22626)Time elapsed: 0.116 s
% 1.61/0.72  % (22626)------------------------------
% 1.61/0.72  % (22626)------------------------------
% 1.61/0.72  % (22482)Success in time 0.361 s
%------------------------------------------------------------------------------
