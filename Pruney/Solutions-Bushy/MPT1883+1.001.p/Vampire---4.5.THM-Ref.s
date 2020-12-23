%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1883+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 365 expanded)
%              Number of leaves         :    6 ( 118 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 (3124 expanded)
%              Number of equality atoms :   29 ( 416 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f43,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f42,f23])).

fof(f23,plain,
    ( v3_tex_2(sK2,sK0)
    | v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ v4_tex_2(sK1,sK0)
      | ~ v3_tex_2(sK2,sK0) )
    & ( v4_tex_2(sK1,sK0)
      | v3_tex_2(sK2,sK0) )
    & u1_struct_0(sK1) = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,
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
              ( ( ~ v4_tex_2(X1,sK0)
                | ~ v3_tex_2(X2,sK0) )
              & ( v4_tex_2(X1,sK0)
                | v3_tex_2(X2,sK0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v4_tex_2(X1,sK0)
              | ~ v3_tex_2(X2,sK0) )
            & ( v4_tex_2(X1,sK0)
              | v3_tex_2(X2,sK0) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ~ v4_tex_2(sK1,sK0)
            | ~ v3_tex_2(X2,sK0) )
          & ( v4_tex_2(sK1,sK0)
            | v3_tex_2(X2,sK0) )
          & u1_struct_0(sK1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ( ~ v4_tex_2(sK1,sK0)
          | ~ v3_tex_2(X2,sK0) )
        & ( v4_tex_2(sK1,sK0)
          | v3_tex_2(X2,sK0) )
        & u1_struct_0(sK1) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v4_tex_2(sK1,sK0)
        | ~ v3_tex_2(sK2,sK0) )
      & ( v4_tex_2(sK1,sK0)
        | v3_tex_2(sK2,sK0) )
      & u1_struct_0(sK1) = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
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
    inference(flattening,[],[f4])).

fof(f4,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
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

fof(f42,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f41,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f20,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_tex_2(sK2,X1)
      | ~ v4_tex_2(sK1,X1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f29,f22])).

fof(f22,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK3(X0,X1),X0)
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK3(X0,X1),X0)
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f54,plain,(
    ~ v3_tex_2(sK2,sK0) ),
    inference(backward_demodulation,[],[f51,f53])).

fof(f53,plain,(
    sK2 = sK3(sK0,sK1) ),
    inference(forward_demodulation,[],[f50,f22])).

fof(f50,plain,(
    u1_struct_0(sK1) = sK3(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f18,f19,f20,f44,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v4_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ~ v4_tex_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f43,f24])).

fof(f24,plain,
    ( ~ v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ~ v3_tex_2(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f18,f19,f20,f44,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tex_2(sK3(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v4_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
