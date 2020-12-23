%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:50 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 283 expanded)
%              Number of leaves         :   15 ( 115 expanded)
%              Depth                    :   22
%              Number of atoms          :  488 (3504 expanded)
%              Number of equality atoms :   26 ( 238 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f324,f346])).

fof(f346,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f345,f219])).

fof(f219,plain,
    ( spl4_13
  <=> v2_compts_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f345,plain,(
    v2_compts_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f344,f41])).

fof(f41,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    & v4_pre_topc(sK3,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & v5_pre_topc(sK2,sK0,sK1)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v5_pre_topc(X2,X0,X1)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v5_pre_topc(X2,sK0,X1)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                & v4_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v5_pre_topc(X2,sK0,X1)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & v8_pre_topc(X1)
            & v1_compts_1(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
              & v4_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v5_pre_topc(X2,sK0,sK1)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & v8_pre_topc(sK1)
          & v1_compts_1(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
            & v4_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v5_pre_topc(X2,sK0,sK1)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & v8_pre_topc(sK1)
        & v1_compts_1(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
          & v4_pre_topc(X3,sK0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v5_pre_topc(sK2,sK0,sK1)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & v8_pre_topc(sK1)
      & v1_compts_1(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
        & v4_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
      & v4_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(f344,plain,
    ( v2_compts_1(sK3,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f343,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f343,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_compts_1(sK3,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f342,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f342,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK3,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f273,f46])).

fof(f46,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f273,plain,
    ( ~ v4_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_compts_1(sK3,sK0)
    | ~ v1_compts_1(sK0) ),
    inference(resolution,[],[f261,f84])).

fof(f84,plain,(
    r1_tarski(sK3,k2_struct_0(sK0)) ),
    inference(resolution,[],[f58,f78])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f69,f63])).

fof(f63,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f45,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_struct_0(X1))
      | ~ v4_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_compts_1(X0,X1)
      | ~ v1_compts_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_tarski(X0,k2_struct_0(X1))
      | ~ v1_compts_1(X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f259,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k2_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f258,f49])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f256,f48])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(u1_struct_0(X0),X0)
      | v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(u1_struct_0(X0),X0)
      | v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f230,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(X2))
      | ~ v2_compts_1(X1,X2)
      | v2_compts_1(X0,X2)
      | ~ v4_pre_topc(X0,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f211,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X2)
      | ~ v2_compts_1(X2,X1)
      | v2_compts_1(X0,X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f54,f59])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f324,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f323,f219])).

fof(f323,plain,(
    ~ v2_compts_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f322,f34])).

fof(f322,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f321,f45])).

fof(f321,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f320,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f320,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f319,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f319,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f318,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f318,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f317,f39])).

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f317,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f316,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f316,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f315,f44])).

fof(f44,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f315,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f299,f43])).

fof(f43,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f299,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f293,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
      | ~ v2_compts_1(X1,X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( v2_compts_1(X1,X0)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v5_pre_topc(X3,X0,X2) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).

fof(f293,plain,(
    ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f292,f40])).

fof(f292,plain,
    ( ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f291,f36])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f291,plain,
    ( ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f290,f37])).

fof(f290,plain,
    ( ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f285,f42])).

fof(f42,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f285,plain,
    ( ~ v8_pre_topc(sK1)
    | ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f197,f47])).

fof(f47,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,(
    ! [X4,X2,X5,X3] :
      ( v4_pre_topc(k7_relset_1(X2,u1_struct_0(X3),X4,X5),X3)
      | ~ v8_pre_topc(X3)
      | ~ v2_compts_1(k7_relset_1(X2,u1_struct_0(X3),X4,X5),X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(X3)))) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n024.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 10:00:51 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.40  % (16063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.17/0.41  % (16063)Refutation found. Thanks to Tanya!
% 0.17/0.41  % SZS status Theorem for theBenchmark
% 0.17/0.42  % (16080)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.17/0.42  % (16072)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.17/0.42  % SZS output start Proof for theBenchmark
% 0.17/0.42  fof(f362,plain,(
% 0.17/0.42    $false),
% 0.17/0.42    inference(avatar_sat_refutation,[],[f324,f346])).
% 0.17/0.42  fof(f346,plain,(
% 0.17/0.42    spl4_13),
% 0.17/0.42    inference(avatar_split_clause,[],[f345,f219])).
% 0.17/0.42  fof(f219,plain,(
% 0.17/0.42    spl4_13 <=> v2_compts_1(sK3,sK0)),
% 0.17/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.17/0.42  fof(f345,plain,(
% 0.17/0.42    v2_compts_1(sK3,sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f344,f41])).
% 0.17/0.42  fof(f41,plain,(
% 0.17/0.42    v1_compts_1(sK0)),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.42  fof(f28,plain,(
% 0.17/0.42    (((~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.17/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f27,f26,f25,f24])).
% 0.17/0.42  fof(f24,plain,(
% 0.17/0.42    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.17/0.42    introduced(choice_axiom,[])).
% 0.17/0.42  fof(f25,plain,(
% 0.17/0.42    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.17/0.42    introduced(choice_axiom,[])).
% 0.17/0.42  fof(f26,plain,(
% 0.17/0.42    ? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.17/0.42    introduced(choice_axiom,[])).
% 0.17/0.42  fof(f27,plain,(
% 0.17/0.42    ? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.17/0.42    introduced(choice_axiom,[])).
% 0.17/0.42  fof(f13,plain,(
% 0.17/0.42    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.17/0.42    inference(flattening,[],[f12])).
% 0.17/0.42  fof(f12,plain,(
% 0.17/0.42    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.17/0.42    inference(ennf_transformation,[],[f11])).
% 0.17/0.42  fof(f11,negated_conjecture,(
% 0.17/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.17/0.42    inference(negated_conjecture,[],[f10])).
% 0.17/0.42  fof(f10,conjecture,(
% 0.17/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).
% 0.17/0.42  fof(f344,plain,(
% 0.17/0.42    v2_compts_1(sK3,sK0) | ~v1_compts_1(sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f343,f33])).
% 0.17/0.42  fof(f33,plain,(
% 0.17/0.42    v2_pre_topc(sK0)),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.42  fof(f343,plain,(
% 0.17/0.42    ~v2_pre_topc(sK0) | v2_compts_1(sK3,sK0) | ~v1_compts_1(sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f342,f34])).
% 0.17/0.42  fof(f34,plain,(
% 0.17/0.42    l1_pre_topc(sK0)),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.42  fof(f342,plain,(
% 0.17/0.42    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_compts_1(sK3,sK0) | ~v1_compts_1(sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f273,f46])).
% 0.17/0.42  fof(f46,plain,(
% 0.17/0.42    v4_pre_topc(sK3,sK0)),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.42  fof(f273,plain,(
% 0.17/0.42    ~v4_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_compts_1(sK3,sK0) | ~v1_compts_1(sK0)),
% 0.17/0.42    inference(resolution,[],[f261,f84])).
% 0.17/0.42  fof(f84,plain,(
% 0.17/0.42    r1_tarski(sK3,k2_struct_0(sK0))),
% 0.17/0.42    inference(resolution,[],[f58,f78])).
% 0.17/0.42  fof(f78,plain,(
% 0.17/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.17/0.42    inference(subsumption_resolution,[],[f69,f63])).
% 0.17/0.42  fof(f63,plain,(
% 0.17/0.42    l1_struct_0(sK0)),
% 0.17/0.42    inference(resolution,[],[f49,f34])).
% 0.17/0.42  fof(f49,plain,(
% 0.17/0.42    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f15])).
% 0.17/0.42  fof(f15,plain,(
% 0.17/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.17/0.42    inference(ennf_transformation,[],[f5])).
% 0.17/0.42  fof(f5,axiom,(
% 0.17/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.17/0.42  fof(f69,plain,(
% 0.17/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0)),
% 0.17/0.42    inference(superposition,[],[f45,f48])).
% 0.17/0.42  fof(f48,plain,(
% 0.17/0.42    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f14])).
% 0.17/0.42  fof(f14,plain,(
% 0.17/0.42    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.17/0.42    inference(ennf_transformation,[],[f4])).
% 0.17/0.42  fof(f4,axiom,(
% 0.17/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.17/0.42  fof(f45,plain,(
% 0.17/0.42    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.42  fof(f58,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f32])).
% 0.17/0.42  fof(f32,plain,(
% 0.17/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.17/0.42    inference(nnf_transformation,[],[f2])).
% 0.17/0.42  fof(f2,axiom,(
% 0.17/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.17/0.42  fof(f261,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_struct_0(X1)) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_compts_1(X0,X1) | ~v1_compts_1(X1)) )),
% 0.17/0.42    inference(duplicate_literal_removal,[],[f260])).
% 0.17/0.42  fof(f260,plain,(
% 0.17/0.42    ( ! [X0,X1] : (v2_compts_1(X0,X1) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_tarski(X0,k2_struct_0(X1)) | ~v1_compts_1(X1) | ~l1_pre_topc(X1)) )),
% 0.17/0.42    inference(resolution,[],[f259,f50])).
% 0.17/0.42  fof(f50,plain,(
% 0.17/0.42    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f29])).
% 0.17/0.42  fof(f29,plain,(
% 0.17/0.42    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 0.17/0.42    inference(nnf_transformation,[],[f16])).
% 0.17/0.42  fof(f16,plain,(
% 0.17/0.42    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.17/0.42    inference(ennf_transformation,[],[f6])).
% 0.17/0.42  fof(f6,axiom,(
% 0.17/0.42    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).
% 0.17/0.42  fof(f259,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~v2_compts_1(k2_struct_0(X0),X0) | v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(X1,k2_struct_0(X0))) )),
% 0.17/0.42    inference(subsumption_resolution,[],[f258,f49])).
% 0.17/0.42  fof(f258,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~v2_compts_1(k2_struct_0(X0),X0) | v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(X1,k2_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.17/0.42    inference(superposition,[],[f256,f48])).
% 0.17/0.42  fof(f256,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~v2_compts_1(u1_struct_0(X0),X0) | v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 0.17/0.42    inference(duplicate_literal_removal,[],[f252])).
% 0.17/0.42  fof(f252,plain,(
% 0.17/0.42    ( ! [X0,X1] : (~v2_compts_1(u1_struct_0(X0),X0) | v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0)) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 0.17/0.42    inference(resolution,[],[f230,f61])).
% 0.17/0.42  fof(f61,plain,(
% 0.17/0.42    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.42    inference(equality_resolution,[],[f56])).
% 0.17/0.42  fof(f56,plain,(
% 0.17/0.42    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.42    inference(cnf_transformation,[],[f31])).
% 0.17/0.42  fof(f31,plain,(
% 0.17/0.42    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.42    inference(flattening,[],[f30])).
% 0.17/0.42  fof(f30,plain,(
% 0.17/0.42    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.42    inference(nnf_transformation,[],[f1])).
% 0.17/0.42  fof(f1,axiom,(
% 0.17/0.42    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.42  fof(f230,plain,(
% 0.17/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,u1_struct_0(X2)) | ~v2_compts_1(X1,X2) | v2_compts_1(X0,X2) | ~v4_pre_topc(X0,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~r1_tarski(X0,u1_struct_0(X2)) | ~r1_tarski(X0,X1)) )),
% 0.17/0.42    inference(resolution,[],[f211,f59])).
% 0.17/0.42  fof(f59,plain,(
% 0.17/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f32])).
% 0.17/0.42  fof(f211,plain,(
% 0.17/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X2) | ~v2_compts_1(X2,X1) | v2_compts_1(X0,X1) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) )),
% 0.17/0.42    inference(resolution,[],[f54,f59])).
% 0.17/0.42  fof(f54,plain,(
% 0.17/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | v2_compts_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.17/0.42    inference(cnf_transformation,[],[f22])).
% 0.17/0.42  fof(f22,plain,(
% 0.17/0.42    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.17/0.42    inference(flattening,[],[f21])).
% 0.17/0.42  fof(f21,plain,(
% 0.17/0.42    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.17/0.42    inference(ennf_transformation,[],[f8])).
% 0.17/0.42  fof(f8,axiom,(
% 0.17/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.17/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.17/0.42  fof(f324,plain,(
% 0.17/0.42    ~spl4_13),
% 0.17/0.42    inference(avatar_split_clause,[],[f323,f219])).
% 0.17/0.42  fof(f323,plain,(
% 0.17/0.42    ~v2_compts_1(sK3,sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f322,f34])).
% 0.17/0.42  fof(f322,plain,(
% 0.17/0.42    ~v2_compts_1(sK3,sK0) | ~l1_pre_topc(sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f321,f45])).
% 0.17/0.42  fof(f321,plain,(
% 0.17/0.42    ~v2_compts_1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.42    inference(subsumption_resolution,[],[f320,f35])).
% 0.17/0.42  fof(f35,plain,(
% 0.17/0.42    ~v2_struct_0(sK1)),
% 0.17/0.42    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f320,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f319,f37])).
% 0.17/0.43  fof(f37,plain,(
% 0.17/0.43    l1_pre_topc(sK1)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f319,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f318,f38])).
% 0.17/0.43  fof(f38,plain,(
% 0.17/0.43    v1_funct_1(sK2)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f318,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f317,f39])).
% 0.17/0.43  fof(f39,plain,(
% 0.17/0.43    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f317,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f316,f40])).
% 0.17/0.43  fof(f40,plain,(
% 0.17/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f316,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f315,f44])).
% 0.17/0.43  fof(f44,plain,(
% 0.17/0.43    v5_pre_topc(sK2,sK0,sK1)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f315,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(subsumption_resolution,[],[f299,f43])).
% 0.17/0.43  fof(f43,plain,(
% 0.17/0.43    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f299,plain,(
% 0.17/0.43    ~v2_compts_1(sK3,sK0) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.17/0.43    inference(resolution,[],[f293,f52])).
% 0.17/0.43  fof(f52,plain,(
% 0.17/0.43    ( ! [X2,X0,X3,X1] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f18])).
% 0.17/0.43  fof(f18,plain,(
% 0.17/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.17/0.43    inference(flattening,[],[f17])).
% 0.17/0.43  fof(f17,plain,(
% 0.17/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | (~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.17/0.43    inference(ennf_transformation,[],[f9])).
% 0.17/0.43  fof(f9,axiom,(
% 0.17/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)) => ((v2_compts_1(X1,X0) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2) & v5_pre_topc(X3,X0,X2)) => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2))))))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).
% 0.17/0.43  fof(f293,plain,(
% 0.17/0.43    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.17/0.43    inference(subsumption_resolution,[],[f292,f40])).
% 0.17/0.43  fof(f292,plain,(
% 0.17/0.43    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.43    inference(subsumption_resolution,[],[f291,f36])).
% 0.17/0.43  fof(f36,plain,(
% 0.17/0.43    v2_pre_topc(sK1)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f291,plain,(
% 0.17/0.43    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.43    inference(subsumption_resolution,[],[f290,f37])).
% 0.17/0.43  fof(f290,plain,(
% 0.17/0.43    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.43    inference(subsumption_resolution,[],[f285,f42])).
% 0.17/0.43  fof(f42,plain,(
% 0.17/0.43    v8_pre_topc(sK1)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f285,plain,(
% 0.17/0.43    ~v8_pre_topc(sK1) | ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.17/0.43    inference(resolution,[],[f197,f47])).
% 0.17/0.43  fof(f47,plain,(
% 0.17/0.43    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f197,plain,(
% 0.17/0.43    ( ! [X4,X2,X5,X3] : (v4_pre_topc(k7_relset_1(X2,u1_struct_0(X3),X4,X5),X3) | ~v8_pre_topc(X3) | ~v2_compts_1(k7_relset_1(X2,u1_struct_0(X3),X4,X5),X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(X3))))) )),
% 0.17/0.43    inference(resolution,[],[f53,f60])).
% 0.17/0.43  fof(f60,plain,(
% 0.17/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.43    inference(cnf_transformation,[],[f23])).
% 0.17/0.43  fof(f23,plain,(
% 0.17/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.43    inference(ennf_transformation,[],[f3])).
% 0.17/0.43  fof(f3,axiom,(
% 0.17/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.17/0.43  fof(f53,plain,(
% 0.17/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f20])).
% 0.17/0.43  fof(f20,plain,(
% 0.17/0.43    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.17/0.43    inference(flattening,[],[f19])).
% 0.17/0.43  fof(f19,plain,(
% 0.17/0.43    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.17/0.43    inference(ennf_transformation,[],[f7])).
% 0.17/0.43  fof(f7,axiom,(
% 0.17/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.17/0.43  % SZS output end Proof for theBenchmark
% 0.17/0.43  % (16063)------------------------------
% 0.17/0.43  % (16063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.43  % (16063)Termination reason: Refutation
% 0.17/0.43  
% 0.17/0.43  % (16063)Memory used [KB]: 6268
% 0.17/0.43  % (16063)Time elapsed: 0.061 s
% 0.17/0.43  % (16063)------------------------------
% 0.17/0.43  % (16063)------------------------------
% 0.17/0.43  % (16056)Success in time 0.107 s
%------------------------------------------------------------------------------
