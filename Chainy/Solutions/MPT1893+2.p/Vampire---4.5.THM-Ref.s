%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1893+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 4.63s
% Output     : Refutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 627 expanded)
%              Number of leaves         :   14 ( 196 expanded)
%              Depth                    :   23
%              Number of atoms          :  545 (5164 expanded)
%              Number of equality atoms :   37 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29305,plain,(
    $false ),
    inference(global_subsumption,[],[f28463,f29304])).

fof(f29304,plain,(
    ~ m1_subset_1(sK17,k1_zfmisc_1(sK17)) ),
    inference(subsumption_resolution,[],[f29303,f4833])).

fof(f4833,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f4406,plain,
    ( v1_subset_1(sK17,u1_struct_0(sK16))
    & v3_tex_2(sK17,sK16)
    & ( v4_pre_topc(sK17,sK16)
      | v3_pre_topc(sK17,sK16) )
    & m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    & l1_pre_topc(sK16)
    & v3_tdlat_3(sK16)
    & v2_pre_topc(sK16)
    & ~ v2_struct_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17])],[f3741,f4405,f4404])).

fof(f4404,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK16))
          & v3_tex_2(X1,sK16)
          & ( v4_pre_topc(X1,sK16)
            | v3_pre_topc(X1,sK16) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK16))) )
      & l1_pre_topc(sK16)
      & v3_tdlat_3(sK16)
      & v2_pre_topc(sK16)
      & ~ v2_struct_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f4405,plain,
    ( ? [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK16))
        & v3_tex_2(X1,sK16)
        & ( v4_pre_topc(X1,sK16)
          | v3_pre_topc(X1,sK16) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK16))) )
   => ( v1_subset_1(sK17,u1_struct_0(sK16))
      & v3_tex_2(sK17,sK16)
      & ( v4_pre_topc(sK17,sK16)
        | v3_pre_topc(sK17,sK16) )
      & m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16))) ) ),
    introduced(choice_axiom,[])).

fof(f3741,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3740])).

fof(f3740,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3719])).

fof(f3719,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3718])).

fof(f3718,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f29303,plain,
    ( ~ m1_subset_1(sK17,k1_zfmisc_1(sK17))
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f29302,f4836])).

fof(f4836,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f29302,plain,
    ( ~ m1_subset_1(sK17,k1_zfmisc_1(sK17))
    | ~ l1_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f29301,f6773])).

fof(f6773,plain,(
    ~ v1_tdlat_3(sK16) ),
    inference(global_subsumption,[],[f4840,f4837,f6772])).

fof(f6772,plain,
    ( ~ v1_subset_1(sK17,u1_struct_0(sK16))
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ v1_tdlat_3(sK16) ),
    inference(subsumption_resolution,[],[f6771,f4833])).

fof(f6771,plain,
    ( ~ v1_subset_1(sK17,u1_struct_0(sK16))
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ v1_tdlat_3(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f6770,f4834])).

fof(f4834,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f6770,plain,
    ( ~ v1_subset_1(sK17,u1_struct_0(sK16))
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ v1_tdlat_3(sK16)
    | ~ v2_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f6757,f4836])).

fof(f6757,plain,
    ( ~ v1_subset_1(sK17,u1_struct_0(sK16))
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ l1_pre_topc(sK16)
    | ~ v1_tdlat_3(sK16)
    | ~ v2_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f4839,f4895])).

fof(f4895,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4422])).

fof(f4422,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3795])).

fof(f3795,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3794])).

fof(f3794,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3705])).

fof(f3705,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f4839,plain,(
    v3_tex_2(sK17,sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f4837,plain,(
    m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16))) ),
    inference(cnf_transformation,[],[f4406])).

fof(f4840,plain,(
    v1_subset_1(sK17,u1_struct_0(sK16)) ),
    inference(cnf_transformation,[],[f4406])).

fof(f29301,plain,
    ( v1_tdlat_3(sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(sK17))
    | ~ l1_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f29122,f6780])).

fof(f6780,plain,(
    v2_tex_2(sK17,sK16) ),
    inference(global_subsumption,[],[f4837,f6779])).

fof(f6779,plain,
    ( v2_tex_2(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16))) ),
    inference(subsumption_resolution,[],[f6759,f4836])).

fof(f6759,plain,
    ( v2_tex_2(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ l1_pre_topc(sK16) ),
    inference(resolution,[],[f4839,f4899])).

fof(f4899,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4428])).

fof(f4428,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK25(X0,X1) != X1
                & r1_tarski(X1,sK25(X0,X1))
                & v2_tex_2(sK25(X0,X1),X0)
                & m1_subset_1(sK25(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f4426,f4427])).

fof(f4427,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK25(X0,X1) != X1
        & r1_tarski(X1,sK25(X0,X1))
        & v2_tex_2(sK25(X0,X1),X0)
        & m1_subset_1(sK25(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4426,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f4425])).

fof(f4425,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4424])).

fof(f4424,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3799])).

fof(f3799,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3798])).

fof(f3798,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3612])).

fof(f3612,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f29122,plain,
    ( ~ v2_tex_2(sK17,sK16)
    | v1_tdlat_3(sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(sK17))
    | ~ l1_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(superposition,[],[f5810,f28296])).

fof(f28296,plain,(
    u1_struct_0(sK16) = sK17 ),
    inference(forward_demodulation,[],[f28295,f27924])).

fof(f27924,plain,(
    sK17 = k2_pre_topc(sK16,sK17) ),
    inference(subsumption_resolution,[],[f27923,f4836])).

fof(f27923,plain,
    ( sK17 = k2_pre_topc(sK16,sK17)
    | ~ l1_pre_topc(sK16) ),
    inference(subsumption_resolution,[],[f27905,f4837])).

fof(f27905,plain,
    ( sK17 = k2_pre_topc(sK16,sK17)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ l1_pre_topc(sK16) ),
    inference(resolution,[],[f27862,f5724])).

fof(f5724,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4321])).

fof(f4321,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4320])).

fof(f4320,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
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

fof(f27862,plain,(
    v4_pre_topc(sK17,sK16) ),
    inference(subsumption_resolution,[],[f27770,f4838])).

fof(f4838,plain,
    ( v3_pre_topc(sK17,sK16)
    | v4_pre_topc(sK17,sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f27770,plain,
    ( ~ v3_pre_topc(sK17,sK16)
    | v4_pre_topc(sK17,sK16) ),
    inference(resolution,[],[f6344,f4837])).

fof(f6344,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ v3_pre_topc(X0,sK16)
      | v4_pre_topc(X0,sK16) ) ),
    inference(global_subsumption,[],[f4836,f6343])).

fof(f6343,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK16)
      | ~ v3_pre_topc(X0,sK16)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ l1_pre_topc(sK16) ) ),
    inference(subsumption_resolution,[],[f6319,f4834])).

fof(f6319,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK16)
      | ~ v3_pre_topc(X0,sK16)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ l1_pre_topc(sK16)
      | ~ v2_pre_topc(sK16) ) ),
    inference(resolution,[],[f4835,f4978])).

fof(f4978,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4473])).

fof(f4473,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK44(X0),X0)
            & v3_pre_topc(sK44(X0),X0)
            & m1_subset_1(sK44(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK44])],[f4471,f4472])).

fof(f4472,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK44(X0),X0)
        & v3_pre_topc(sK44(X0),X0)
        & m1_subset_1(sK44(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4471,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f4470])).

fof(f4470,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3841])).

fof(f3841,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3840])).

fof(f3840,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3675])).

fof(f3675,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f4835,plain,(
    v3_tdlat_3(sK16) ),
    inference(cnf_transformation,[],[f4406])).

fof(f28295,plain,(
    u1_struct_0(sK16) = k2_pre_topc(sK16,sK17) ),
    inference(subsumption_resolution,[],[f28294,f4836])).

fof(f28294,plain,
    ( u1_struct_0(sK16) = k2_pre_topc(sK16,sK17)
    | ~ l1_pre_topc(sK16) ),
    inference(subsumption_resolution,[],[f28281,f4837])).

fof(f28281,plain,
    ( u1_struct_0(sK16) = k2_pre_topc(sK16,sK17)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ l1_pre_topc(sK16) ),
    inference(resolution,[],[f28124,f5197])).

fof(f5197,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4577])).

fof(f4577,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4002])).

fof(f4002,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3604])).

fof(f3604,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f28124,plain,(
    v1_tops_1(sK17,sK16) ),
    inference(resolution,[],[f28111,f6769])).

fof(f6769,plain,
    ( ~ v3_pre_topc(sK17,sK16)
    | v1_tops_1(sK17,sK16) ),
    inference(global_subsumption,[],[f4837,f6768])).

fof(f6768,plain,
    ( v1_tops_1(sK17,sK16)
    | ~ v3_pre_topc(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16))) ),
    inference(subsumption_resolution,[],[f6767,f4833])).

fof(f6767,plain,
    ( v1_tops_1(sK17,sK16)
    | ~ v3_pre_topc(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f6766,f4834])).

fof(f6766,plain,
    ( v1_tops_1(sK17,sK16)
    | ~ v3_pre_topc(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ v2_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f6756,f4836])).

fof(f6756,plain,
    ( v1_tops_1(sK17,sK16)
    | ~ v3_pre_topc(sK17,sK16)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ l1_pre_topc(sK16)
    | ~ v2_pre_topc(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f4839,f4893])).

fof(f4893,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3791])).

fof(f3791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3790])).

fof(f3790,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3703])).

fof(f3703,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f28111,plain,(
    v3_pre_topc(sK17,sK16) ),
    inference(subsumption_resolution,[],[f28019,f27862])).

fof(f28019,plain,
    ( ~ v4_pre_topc(sK17,sK16)
    | v3_pre_topc(sK17,sK16) ),
    inference(resolution,[],[f6346,f4837])).

fof(f6346,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ v4_pre_topc(X1,sK16)
      | v3_pre_topc(X1,sK16) ) ),
    inference(global_subsumption,[],[f4836,f6345])).

fof(f6345,plain,(
    ! [X1] :
      ( v3_pre_topc(X1,sK16)
      | ~ v4_pre_topc(X1,sK16)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ l1_pre_topc(sK16) ) ),
    inference(subsumption_resolution,[],[f6320,f4834])).

fof(f6320,plain,(
    ! [X1] :
      ( v3_pre_topc(X1,sK16)
      | ~ v4_pre_topc(X1,sK16)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK16)))
      | ~ l1_pre_topc(sK16)
      | ~ v2_pre_topc(sK16) ) ),
    inference(resolution,[],[f4835,f4982])).

fof(f4982,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4477])).

fof(f4477,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK45(X0),X0)
            & v4_pre_topc(sK45(X0),X0)
            & m1_subset_1(sK45(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK45])],[f4475,f4476])).

fof(f4476,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK45(X0),X0)
        & v4_pre_topc(sK45(X0),X0)
        & m1_subset_1(sK45(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4475,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f4474])).

fof(f4474,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3843])).

fof(f3843,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3842])).

fof(f3842,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3677])).

fof(f3677,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f5810,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f5246])).

fof(f5246,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4605])).

fof(f4605,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4036])).

fof(f4036,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4035])).

fof(f4035,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3681])).

fof(f3681,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f28463,plain,(
    m1_subset_1(sK17,k1_zfmisc_1(sK17)) ),
    inference(backward_demodulation,[],[f4837,f28296])).
%------------------------------------------------------------------------------
