%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1746+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 (1095 expanded)
%              Number of leaves         :    7 ( 384 expanded)
%              Depth                    :   33
%              Number of atoms          :  601 (20155 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f216,f207])).

fof(f207,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f206,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK0)) )
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) )
    & ( ! [X4] :
          ( r1_tmap_1(sK0,sK1,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(sK2,sK0,sK1)
        & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(sK2) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(sK0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,sK0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(sK0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,sK0,X1)
                  & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(sK0,X1,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,sK0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ! [X4] :
                  ( r1_tmap_1(sK0,X1,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v5_pre_topc(X2,sK0,X1)
                & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(sK0,sK1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(X2,sK0,sK1)
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(X2) )
          & ( ! [X4] :
                ( r1_tmap_1(sK0,sK1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(X2,sK0,sK1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X2) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_tmap_1(sK0,sK1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(X2,sK0,sK1)
          | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(X2) )
        & ( ! [X4] :
              ( r1_tmap_1(sK0,sK1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(X2,sK0,sK1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X2) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
      & ( ! [X4] :
            ( r1_tmap_1(sK0,sK1,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(sK2,sK0,sK1)
          & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(sK2) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK0,sK1,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(X0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tmap_1)).

fof(f206,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f205,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f202])).

fof(f202,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f183,f201])).

fof(f201,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f200,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f200,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f199,f24])).

fof(f24,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f199,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f198,f25])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f198,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f197,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f197,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f196,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f196,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f195,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f195,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f194,f26])).

fof(f194,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f193,f27])).

fof(f193,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f192,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f192,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f147,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f147,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f31,f28,f146])).

fof(f146,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f145,f23])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f144,f24])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f143,f25])).

fof(f143,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f142,f20])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f141,f21])).

fof(f141,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f140,f22])).

fof(f140,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f137,f26])).

fof(f137,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X4] :
      ( r1_tmap_1(sK0,sK1,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f183,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f182,f23])).

fof(f182,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f181,f24])).

fof(f181,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f180,f25])).

fof(f180,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f179,f20])).

fof(f179,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f178,f21])).

fof(f178,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f177,f22])).

fof(f177,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f176,f26])).

fof(f176,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f165,f27])).

fof(f165,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f204,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f33,f28])).

fof(f33,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f216,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f215,f147])).

fof(f215,plain,(
    ~ r1_tmap_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f214,f26])).

fof(f214,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f213,f27])).

fof(f213,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f212,f202])).

fof(f212,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f34,f28])).

fof(f34,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

% (3581)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark

%------------------------------------------------------------------------------
