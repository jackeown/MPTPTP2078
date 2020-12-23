%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1883+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 410 expanded)
%              Number of leaves         :    6 ( 130 expanded)
%              Depth                    :   23
%              Number of atoms          :  241 (3457 expanded)
%              Number of equality atoms :   32 ( 461 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6291,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6290,f5884])).

fof(f5884,plain,(
    v3_tex_2(sK8,sK6) ),
    inference(subsumption_resolution,[],[f5883,f4208])).

fof(f4208,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f4025])).

fof(f4025,plain,
    ( ( ~ v4_tex_2(sK7,sK6)
      | ~ v3_tex_2(sK8,sK6) )
    & ( v4_tex_2(sK7,sK6)
      | v3_tex_2(sK8,sK6) )
    & u1_struct_0(sK7) = sK8
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_pre_topc(sK7,sK6)
    & l1_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f4021,f4024,f4023,f4022])).

fof(f4022,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) )
                & ( v4_tex_2(X1,X0)
                  | v3_tex_2(X2,X0) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,sK6)
                | ~ v3_tex_2(X2,sK6) )
              & ( v4_tex_2(X1,sK6)
                | v3_tex_2(X2,sK6) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
          & m1_pre_topc(X1,sK6) )
      & l1_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f4023,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v4_tex_2(X1,sK6)
              | ~ v3_tex_2(X2,sK6) )
            & ( v4_tex_2(X1,sK6)
              | v3_tex_2(X2,sK6) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_pre_topc(X1,sK6) )
   => ( ? [X2] :
          ( ( ~ v4_tex_2(sK7,sK6)
            | ~ v3_tex_2(X2,sK6) )
          & ( v4_tex_2(sK7,sK6)
            | v3_tex_2(X2,sK6) )
          & u1_struct_0(sK7) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & m1_pre_topc(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f4024,plain,
    ( ? [X2] :
        ( ( ~ v4_tex_2(sK7,sK6)
          | ~ v3_tex_2(X2,sK6) )
        & ( v4_tex_2(sK7,sK6)
          | v3_tex_2(X2,sK6) )
        & u1_struct_0(sK7) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ( ~ v4_tex_2(sK7,sK6)
        | ~ v3_tex_2(sK8,sK6) )
      & ( v4_tex_2(sK7,sK6)
        | v3_tex_2(sK8,sK6) )
      & u1_struct_0(sK7) = sK8
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f4021,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4020])).

fof(f4020,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3737])).

fof(f3737,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3736])).

fof(f3736,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3704])).

fof(f3704,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v3_tex_2(X2,X0)
                  <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3703])).

fof(f3703,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

fof(f5883,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | v3_tex_2(sK8,sK6) ),
    inference(forward_demodulation,[],[f5882,f4209])).

fof(f4209,plain,(
    u1_struct_0(sK7) = sK8 ),
    inference(cnf_transformation,[],[f4025])).

fof(f5882,plain,
    ( v3_tex_2(sK8,sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(duplicate_literal_removal,[],[f5881])).

fof(f5881,plain,
    ( v3_tex_2(sK8,sK6)
    | v3_tex_2(sK8,sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f5880,f4209])).

fof(f5880,plain,
    ( v3_tex_2(sK8,sK6)
    | v3_tex_2(u1_struct_0(sK7),sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f5879,f4205])).

fof(f4205,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f4025])).

fof(f5879,plain,
    ( v3_tex_2(sK8,sK6)
    | v3_tex_2(u1_struct_0(sK7),sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f5878,f4206])).

fof(f4206,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f4025])).

fof(f5878,plain,
    ( v3_tex_2(sK8,sK6)
    | v3_tex_2(u1_struct_0(sK7),sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f5877,f4207])).

fof(f4207,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f4025])).

fof(f5877,plain,
    ( v3_tex_2(sK8,sK6)
    | v3_tex_2(u1_struct_0(sK7),sK6)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_pre_topc(sK7,sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f4210,f4604])).

fof(f4604,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4212])).

fof(f4212,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4029])).

fof(f4029,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK9(X0,X1),X0)
                & u1_struct_0(X1) = sK9(X0,X1)
                & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f4027,f4028])).

fof(f4028,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK9(X0,X1),X0)
        & u1_struct_0(X1) = sK9(X0,X1)
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4027,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4026])).

fof(f4026,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3739])).

fof(f3739,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3738])).

fof(f3738,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3611])).

fof(f3611,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(f4210,plain,
    ( v4_tex_2(sK7,sK6)
    | v3_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f4025])).

fof(f6290,plain,(
    ~ v3_tex_2(sK8,sK6) ),
    inference(forward_demodulation,[],[f6064,f6061])).

fof(f6061,plain,(
    sK8 = sK9(sK6,sK7) ),
    inference(forward_demodulation,[],[f6060,f4209])).

fof(f6060,plain,(
    u1_struct_0(sK7) = sK9(sK6,sK7) ),
    inference(subsumption_resolution,[],[f6059,f4205])).

fof(f6059,plain,
    ( u1_struct_0(sK7) = sK9(sK6,sK7)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f6058,f4206])).

fof(f6058,plain,
    ( u1_struct_0(sK7) = sK9(sK6,sK7)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f6053,f4207])).

fof(f6053,plain,
    ( u1_struct_0(sK7) = sK9(sK6,sK7)
    | ~ m1_pre_topc(sK7,sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f6050,f4214])).

fof(f4214,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK9(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4029])).

fof(f6050,plain,(
    ~ v4_tex_2(sK7,sK6) ),
    inference(subsumption_resolution,[],[f4211,f5884])).

fof(f4211,plain,
    ( ~ v4_tex_2(sK7,sK6)
    | ~ v3_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f4025])).

fof(f6064,plain,(
    ~ v3_tex_2(sK9(sK6,sK7),sK6) ),
    inference(subsumption_resolution,[],[f6063,f4205])).

fof(f6063,plain,
    ( ~ v3_tex_2(sK9(sK6,sK7),sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f6062,f4206])).

fof(f6062,plain,
    ( ~ v3_tex_2(sK9(sK6,sK7),sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f6054,f4207])).

fof(f6054,plain,
    ( ~ v3_tex_2(sK9(sK6,sK7),sK6)
    | ~ m1_pre_topc(sK7,sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f6050,f4215])).

fof(f4215,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK9(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4029])).
%------------------------------------------------------------------------------
