%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 (1466 expanded)
%              Number of leaves         :   14 ( 606 expanded)
%              Depth                    :   22
%              Number of atoms          :  407 (12380 expanded)
%              Number of equality atoms :   32 ( 155 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(resolution,[],[f234,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f234,plain,(
    ~ r1_tarski(sK3,sK3) ),
    inference(global_subsumption,[],[f72,f217,f233])).

fof(f233,plain,
    ( ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ r1_tarski(sK3,sK3)
    | v4_tops_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f232,f195])).

fof(f195,plain,(
    sK3 = k1_tops_1(sK1,sK3) ),
    inference(backward_demodulation,[],[f102,f193])).

fof(f193,plain,(
    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f95,f192])).

fof(f192,plain,(
    v6_tops_1(sK3,sK1) ),
    inference(global_subsumption,[],[f64,f65,f116,f190])).

fof(f190,plain,
    ( sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f187,f63])).

fof(f63,plain,
    ( v3_pre_topc(sK4,sK2)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,
    ( sP0(sK2,sK4)
    | v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ( ( ~ v4_tops_1(sK3,sK1)
          | ~ v3_pre_topc(sK3,sK1) )
        & v6_tops_1(sK3,sK1) )
      | sP0(sK2,sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | sP0(X1,X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK1)
                        | ~ v3_pre_topc(X2,sK1) )
                      & v6_tops_1(X2,sK1) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK1)
                      | ~ v3_pre_topc(X2,sK1) )
                    & v6_tops_1(X2,sK1) )
                  | sP0(X1,X3) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK1)
                    | ~ v3_pre_topc(X2,sK1) )
                  & v6_tops_1(X2,sK1) )
                | sP0(sK2,X3) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK1)
                  | ~ v3_pre_topc(X2,sK1) )
                & v6_tops_1(X2,sK1) )
              | sP0(sK2,X3) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK3,sK1)
                | ~ v3_pre_topc(sK3,sK1) )
              & v6_tops_1(sK3,sK1) )
            | sP0(sK2,X3) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK3,sK1)
              | ~ v3_pre_topc(sK3,sK1) )
            & v6_tops_1(sK3,sK1) )
          | sP0(sK2,X3) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ( ( ~ v4_tops_1(sK3,sK1)
            | ~ v3_pre_topc(sK3,sK1) )
          & v6_tops_1(sK3,sK1) )
        | sP0(sK2,sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f24])).

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ v6_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v3_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X3] :
      ( ( ~ v6_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v3_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f187,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(global_subsumption,[],[f45,f74,f185])).

fof(f185,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK4,k2_pre_topc(sK2,sK4))
    | ~ v3_pre_topc(sK4,sK2)
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f179,f130])).

fof(f130,plain,
    ( ~ r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
    | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f127,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f127,plain,
    ( r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4)
    | ~ v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_tops_1(X1,sK2)
      | r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,X1)),X1) ) ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f179,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_tops_1(sK2,k2_pre_topc(sK2,sK4)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,k2_pre_topc(sK2,sK4))
      | ~ v3_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f152,f45])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X1,k2_pre_topc(sK2,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X1,k1_tops_1(sK2,k2_pre_topc(sK2,X2)))
      | ~ v3_pre_topc(X1,sK2) ) ),
    inference(global_subsumption,[],[f43,f151])).

fof(f151,plain,(
    ! [X2,X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ r1_tarski(X1,k2_pre_topc(sK2,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X1,k1_tops_1(sK2,k2_pre_topc(sK2,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f142,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f142,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X2,sK2)
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X2,k1_tops_1(sK2,X3)) ) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f74,plain,(
    r1_tarski(sK4,k2_pre_topc(sK2,sK4)) ),
    inference(resolution,[],[f71,f45])).

fof(f71,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_tarski(X1,k2_pre_topc(sK2,X1)) ) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f116,plain,
    ( sK4 != k1_tops_1(sK2,k2_pre_topc(sK2,sK4))
    | v6_tops_1(sK4,sK2) ),
    inference(resolution,[],[f110,f45])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_tops_1(sK2,k2_pre_topc(sK2,X1)) != X1
      | v6_tops_1(X1,sK2) ) ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f65,plain,
    ( ~ v6_tops_1(sK4,sK2)
    | v6_tops_1(sK3,sK1) ),
    inference(resolution,[],[f40,f46])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f64,plain,
    ( v6_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f90,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v6_tops_1(X0,sK1)
      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(resolution,[],[f88,f44])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) ) ),
    inference(global_subsumption,[],[f42,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0)) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f232,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f230,f193])).

fof(f230,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | v4_tops_1(sK3,sK1) ),
    inference(resolution,[],[f182,f44])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0)))
      | v4_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f217,plain,(
    ~ v4_tops_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f191,f211])).

fof(f211,plain,(
    v3_pre_topc(sK3,sK1) ),
    inference(global_subsumption,[],[f44,f210])).

fof(f210,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK3,sK1) ),
    inference(forward_demodulation,[],[f203,f195])).

fof(f203,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f89,f195])).

fof(f89,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k1_tops_1(sK1,sK3),sK1) ),
    inference(superposition,[],[f77,f86])).

fof(f86,plain,(
    k1_tops_1(sK1,sK3) = k1_tops_1(sK1,k1_tops_1(sK1,sK3)) ),
    inference(resolution,[],[f84,f44])).

fof(f77,plain,(
    ! [X0] :
      ( v3_pre_topc(k1_tops_1(sK1,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(global_subsumption,[],[f42,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | v3_pre_topc(k1_tops_1(sK1,X0),sK1) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f191,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(global_subsumption,[],[f66,f67,f68,f116,f187])).

fof(f68,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v4_tops_1(sK3,sK1)
    | ~ v3_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,
    ( sP0(sK2,sK4)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | v4_tops_1(sK4,sK2) ),
    inference(resolution,[],[f47,f39])).

fof(f66,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | ~ v4_tops_1(sK3,sK1)
    | ~ v6_tops_1(sK4,sK2) ),
    inference(resolution,[],[f47,f40])).

fof(f72,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ) ),
    inference(resolution,[],[f48,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:14:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (16255)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.47  % (16247)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.47  % (16249)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (16241)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.48  % (16247)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (16239)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(resolution,[],[f234,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    ~r1_tarski(sK3,sK3)),
% 0.22/0.49    inference(global_subsumption,[],[f72,f217,f233])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~r1_tarski(sK3,sK3) | v4_tops_1(sK3,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f232,f195])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    sK3 = k1_tops_1(sK1,sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f102,f193])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.22/0.49    inference(subsumption_resolution,[],[f95,f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    v6_tops_1(sK3,sK1)),
% 0.22/0.49    inference(global_subsumption,[],[f64,f65,f116,f190])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2) | v6_tops_1(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f187,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    v3_pre_topc(sK4,sK2) | v6_tops_1(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f38,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    sP0(sK2,sK4) | v6_tops_1(sK3,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ((((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31,f30,f29,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK1) | ~v3_pre_topc(X2,sK1)) & v6_tops_1(X2,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ? [X3] : ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => ((((~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)) & v6_tops_1(sK3,sK1)) | sP0(sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(definition_folding,[],[f12,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v3_pre_topc(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((~v6_tops_1(X1,X0) & v4_tops_1(X1,X0) & v3_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 0.22/0.49    inference(rectify,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X1,X3] : ((~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.22/0.49    inference(nnf_transformation,[],[f24])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~v3_pre_topc(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(global_subsumption,[],[f45,f74,f185])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK4,k2_pre_topc(sK2,sK4)) | ~v3_pre_topc(sK4,sK2) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f179,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~r1_tarski(sK4,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | sK4 = k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | ~v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f127,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,sK4)),sK4) | ~v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f122,f45])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_tops_1(X1,sK2) | r1_tarski(k1_tops_1(sK2,k2_pre_topc(sK2,X1)),X1)) )),
% 0.22/0.49    inference(resolution,[],[f51,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    l1_pre_topc(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK2,k2_pre_topc(sK2,sK4))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,k2_pre_topc(sK2,sK4)) | ~v3_pre_topc(X0,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f152,f45])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X1,k2_pre_topc(sK2,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X1,k1_tops_1(sK2,k2_pre_topc(sK2,X2))) | ~v3_pre_topc(X1,sK2)) )),
% 0.22/0.49    inference(global_subsumption,[],[f43,f151])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v3_pre_topc(X1,sK2) | ~r1_tarski(X1,k2_pre_topc(sK2,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X1,k1_tops_1(sK2,k2_pre_topc(sK2,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) )),
% 0.22/0.49    inference(resolution,[],[f142,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X2,sK2) | ~r1_tarski(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X2,k1_tops_1(sK2,X3))) )),
% 0.22/0.49    inference(resolution,[],[f54,f43])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    r1_tarski(sK4,k2_pre_topc(sK2,sK4))),
% 0.22/0.49    inference(resolution,[],[f71,f45])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | r1_tarski(X1,k2_pre_topc(sK2,X1))) )),
% 0.22/0.49    inference(resolution,[],[f48,f43])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    sK4 != k1_tops_1(sK2,k2_pre_topc(sK2,sK4)) | v6_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f110,f45])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tops_1(sK2,k2_pre_topc(sK2,X1)) != X1 | v6_tops_1(X1,sK2)) )),
% 0.22/0.49    inference(resolution,[],[f50,f43])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v6_tops_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ~v6_tops_1(sK4,sK2) | v6_tops_1(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f40,f46])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | ~v6_tops_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v6_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f39,f46])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v6_tops_1(sK3,sK1) | sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 0.22/0.49    inference(resolution,[],[f90,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v6_tops_1(X0,sK1) | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = X0) )),
% 0.22/0.49    inference(resolution,[],[f49,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    l1_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 0.22/0.49    inference(resolution,[],[f88,f44])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f42,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tops_1(sK1,k2_pre_topc(sK1,X0)) = k1_tops_1(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 0.22/0.49    inference(resolution,[],[f84,f56])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k1_tops_1(sK1,X0) = k1_tops_1(sK1,k1_tops_1(sK1,X0))) )),
% 0.22/0.49    inference(resolution,[],[f57,f42])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ~r1_tarski(sK3,sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f230,f193])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | v4_tops_1(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f182,f44])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(sK1,k1_tops_1(sK1,X0))) | v4_tops_1(X0,sK1)) )),
% 0.22/0.49    inference(resolution,[],[f53,f42])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_tops_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    ~v4_tops_1(sK3,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f191,f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    v3_pre_topc(sK3,sK1)),
% 0.22/0.49    inference(global_subsumption,[],[f44,f210])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK3,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f203,f195])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    v3_pre_topc(sK3,sK1) | ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.49    inference(backward_demodulation,[],[f89,f195])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(k1_tops_1(sK1,sK3),sK1)),
% 0.22/0.49    inference(superposition,[],[f77,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k1_tops_1(sK1,sK3) = k1_tops_1(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.49    inference(resolution,[],[f84,f44])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X0] : (v3_pre_topc(k1_tops_1(sK1,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f42,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v3_pre_topc(k1_tops_1(sK1,X0),sK1)) )),
% 0.22/0.49    inference(resolution,[],[f55,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v2_pre_topc(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)),
% 0.22/0.49    inference(global_subsumption,[],[f66,f67,f68,f116,f187])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v3_pre_topc(sK4,sK2) | ~v4_tops_1(sK3,sK1) | ~v3_pre_topc(sK3,sK1)),
% 0.22/0.49    inference(resolution,[],[f47,f38])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    sP0(sK2,sK4) | ~v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ~v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1) | v4_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f47,f39])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~v3_pre_topc(sK3,sK1) | ~v4_tops_1(sK3,sK1) | ~v6_tops_1(sK4,sK2)),
% 0.22/0.49    inference(resolution,[],[f47,f40])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.22/0.49    inference(resolution,[],[f70,f44])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X0,k2_pre_topc(sK1,X0))) )),
% 0.22/0.49    inference(resolution,[],[f48,f42])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (16247)------------------------------
% 0.22/0.49  % (16247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16247)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (16247)Memory used [KB]: 6524
% 0.22/0.49  % (16247)Time elapsed: 0.069 s
% 0.22/0.49  % (16247)------------------------------
% 0.22/0.49  % (16247)------------------------------
% 0.22/0.50  % (16234)Success in time 0.129 s
%------------------------------------------------------------------------------
