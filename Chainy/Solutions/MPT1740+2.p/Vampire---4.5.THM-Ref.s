%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1740+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  181 (13443 expanded)
%              Number of leaves         :   12 (4772 expanded)
%              Depth                    :  102
%              Number of atoms          : 1422 (182355 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4390,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4389,f3507])).

fof(f3507,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3454,plain,
    ( ( ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ v5_pre_topc(sK2,sK1,sK0) )
    & ( ! [X4] :
          ( r1_tmap_1(sK1,sK0,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | v5_pre_topc(sK2,sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3449,f3453,f3452,f3451,f3450])).

fof(f3450,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | v5_pre_topc(X2,X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
                    ( ~ r1_tmap_1(X1,sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,sK0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,sK0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3451,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(X1,sK0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v5_pre_topc(X2,X1,sK0) )
            & ( ! [X4] :
                  ( r1_tmap_1(X1,sK0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | v5_pre_topc(X2,X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(sK1,sK0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            | ~ v5_pre_topc(X2,sK1,sK0) )
          & ( ! [X4] :
                ( r1_tmap_1(sK1,sK0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
            | v5_pre_topc(X2,sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3452,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ~ r1_tmap_1(sK1,sK0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          | ~ v5_pre_topc(X2,sK1,sK0) )
        & ( ! [X4] :
              ( r1_tmap_1(sK1,sK0,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
          | v5_pre_topc(X2,sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( ~ r1_tmap_1(sK1,sK0,sK2,X3)
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        | ~ v5_pre_topc(sK2,sK1,sK0) )
      & ( ! [X4] :
            ( r1_tmap_1(sK1,sK0,sK2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
        | v5_pre_topc(sK2,sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3453,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK1,sK0,sK2,X3)
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f3449,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f3448])).

fof(f3448,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3447])).

fof(f3447,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3404])).

fof(f3404,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3403])).

fof(f3403,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3392])).

fof(f3392,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3391])).

fof(f3391,conjecture,(
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

fof(f4389,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4388,f3508])).

fof(f3508,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4388,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4387,f3509])).

fof(f3509,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4387,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4386,f3504])).

fof(f3504,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4386,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4385,f3505])).

fof(f3505,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4385,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4384,f3506])).

fof(f3506,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4384,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4383,f3510])).

fof(f3510,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4383,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4382,f3511])).

fof(f3511,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4382,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4381,f3512])).

fof(f3512,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4380,f4184])).

fof(f4184,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3514,f4183])).

fof(f4183,plain,(
    v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f4182,f3507])).

fof(f4182,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4181,f3508])).

fof(f4181,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4180,f3509])).

fof(f4180,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4179,f3504])).

fof(f4179,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4178,f3505])).

fof(f4178,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4177,f3506])).

fof(f4177,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4176,f3510])).

fof(f4176,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4175,f3511])).

fof(f4175,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4174,f3512])).

fof(f4174,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f4173])).

fof(f4173,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4163,f3551])).

fof(f3551,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK13(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK12(X0,X1,X2)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3487])).

fof(f3487,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ! [X5] :
                        ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK13(X0,X1,X2))
                        | ~ m1_connsp_2(X5,X0,sK12(X0,X1,X2)) )
                    & m1_connsp_2(sK13(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK12(X0,X1,X2)))
                    & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK14(X0,X1,X2,X6,X7)),X7)
                            & m1_connsp_2(sK14(X0,X1,X2,X6,X7),X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f3483,f3486,f3485,f3484])).

fof(f3484,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                  | ~ m1_connsp_2(X5,X0,X3) )
              & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ! [X5] :
                ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                | ~ m1_connsp_2(X5,X0,sK12(X0,X1,X2)) )
            & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK12(X0,X1,X2))) )
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3485,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,sK12(X0,X1,X2)) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK12(X0,X1,X2))) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK13(X0,X1,X2))
            | ~ m1_connsp_2(X5,X0,sK12(X0,X1,X2)) )
        & m1_connsp_2(sK13(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK12(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3486,plain,(
    ! [X7,X6,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
          & m1_connsp_2(X8,X0,X6) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK14(X0,X1,X2,X6,X7)),X7)
        & m1_connsp_2(sK14(X0,X1,X2,X6,X7),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f3483,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ? [X8] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
                              & m1_connsp_2(X8,X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3482])).

fof(f3482,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3424])).

fof(f3424,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3423])).

fof(f3423,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3328])).

fof(f3328,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).

fof(f4163,plain,
    ( ~ m1_connsp_2(sK13(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f4162])).

fof(f4162,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK13(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2))) ),
    inference(resolution,[],[f4152,f4037])).

fof(f4037,plain,(
    ! [X0] :
      ( m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2))) ) ),
    inference(subsumption_resolution,[],[f4036,f3803])).

fof(f3803,plain,
    ( m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f3802,f3510])).

fof(f3802,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f3800,f3512])).

fof(f3800,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(resolution,[],[f3737,f3511])).

fof(f3737,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK12(sK1,sK0,X0),u1_struct_0(sK1))
      | v5_pre_topc(X0,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f3736,f3504])).

fof(f3736,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | m1_subset_1(sK12(sK1,sK0,X0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | v5_pre_topc(X0,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f3734,f3506])).

fof(f3734,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(sK12(sK1,sK0,X0),u1_struct_0(sK1))
      | v2_struct_0(sK0)
      | v5_pre_topc(X0,sK1,sK0) ) ),
    inference(resolution,[],[f3656,f3505])).

fof(f3656,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | m1_subset_1(sK12(sK1,X2,X3),u1_struct_0(sK1))
      | v2_struct_0(X2)
      | v5_pre_topc(X3,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f3655,f3507])).

fof(f3655,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK12(sK1,X2,X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v5_pre_topc(X3,sK1,X2)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3652,f3509])).

fof(f3652,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK12(sK1,X2,X3),u1_struct_0(sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK1)
      | v5_pre_topc(X3,sK1,X2)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3550,f3508])).

fof(f3550,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3487])).

fof(f4036,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4035,f3504])).

fof(f4035,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4034,f3505])).

fof(f4034,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4033,f3506])).

fof(f4033,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4032,f3510])).

fof(f4032,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4031,f3511])).

fof(f4031,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4030,f3512])).

fof(f4030,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f4029])).

fof(f4029,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1))
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(resolution,[],[f3815,f3513])).

fof(f3513,plain,(
    ! [X4] :
      ( r1_tmap_1(sK1,sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f3454])).

fof(f3815,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(sK1,X1,X2,sK12(sK1,sK0,sK2))
      | ~ m1_connsp_2(X0,X1,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | m1_connsp_2(sK5(sK1,X1,X2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f3814,f3507])).

fof(f3814,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X0,X1,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X2,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X1,X2,sK12(sK1,sK0,sK2))
      | m1_connsp_2(sK5(sK1,X1,X2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3813,f3508])).

fof(f3813,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X0,X1,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X2,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X1,X2,sK12(sK1,sK0,sK2))
      | m1_connsp_2(sK5(sK1,X1,X2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3804,f3509])).

fof(f3804,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X0,X1,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X2,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X1,X2,sK12(sK1,sK0,sK2))
      | m1_connsp_2(sK5(sK1,X1,X2,sK12(sK1,sK0,sK2),X0),sK1,sK12(sK1,sK0,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3803,f3516])).

fof(f3516,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | m1_connsp_2(sK5(X0,X1,X2,X3,X6),X0,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f3459,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK4(X0,X1,X2,X3))
                            | ~ m1_connsp_2(X5,X0,X3) )
                        & m1_connsp_2(sK4(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2,X3,X6)),X6)
                            & m1_connsp_2(sK5(X0,X1,X2,X3,X6),X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3456,f3458,f3457])).

fof(f3457,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK4(X0,X1,X2,X3))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK4(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3458,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & m1_connsp_2(X7,X0,X3) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2,X3,X6)),X6)
        & m1_connsp_2(sK5(X0,X1,X2,X3,X6),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f3456,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & m1_connsp_2(X7,X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3455])).

fof(f3455,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3406])).

fof(f3406,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3405])).

fof(f3405,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3326])).

fof(f3326,axiom,(
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).

fof(f4152,plain,
    ( ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f4151,f3507])).

fof(f4151,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4150,f3508])).

fof(f4150,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4149,f3509])).

fof(f4149,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4148,f3504])).

fof(f4148,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4147,f3505])).

fof(f4147,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4146,f3506])).

fof(f4146,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4145,f3510])).

fof(f4145,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4144,f3511])).

fof(f4144,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4143,f3512])).

fof(f4143,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f4124])).

fof(f4124,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_connsp_2(sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2)),sK1,sK12(sK1,sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4123,f3552])).

fof(f3552,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK13(X0,X1,X2))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(X5,X0,sK12(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3487])).

fof(f4123,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f4122,f3507])).

fof(f4122,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4121,f3508])).

fof(f4121,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4120,f3509])).

fof(f4120,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4119,f3504])).

fof(f4119,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4118,f3505])).

fof(f4118,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4117,f3506])).

fof(f4117,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4116,f3510])).

fof(f4116,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4115,f3511])).

fof(f4115,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4114,f3512])).

fof(f4114,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f4111])).

fof(f4111,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),sK13(sK1,sK0,sK2))),sK13(sK1,sK0,sK2))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4049,f3551])).

fof(f4049,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0) ) ),
    inference(subsumption_resolution,[],[f4048,f3803])).

fof(f4048,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4047,f3504])).

fof(f4047,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4046,f3505])).

fof(f4046,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4045,f3506])).

fof(f4045,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4044,f3510])).

fof(f4044,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4043,f3511])).

fof(f4043,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f4042,f3512])).

fof(f4042,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f4041])).

fof(f4041,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK5(sK1,sK0,sK2,sK12(sK1,sK0,sK2),X0)),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK12(sK1,sK0,sK2),u1_struct_0(sK1))
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(resolution,[],[f3818,f3513])).

fof(f3818,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK1,X4,X5,sK12(sK1,sK0,sK2))
      | ~ m1_connsp_2(X3,X4,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X4),X5,sK12(sK1,sK0,sK2)))
      | v5_pre_topc(sK2,sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X4),X5,sK5(sK1,X4,X5,sK12(sK1,sK0,sK2),X3)),X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f3817,f3507])).

fof(f3817,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X3,X4,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X4),X5,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X4,X5,sK12(sK1,sK0,sK2))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X4),X5,sK5(sK1,X4,X5,sK12(sK1,sK0,sK2),X3)),X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3816,f3508])).

fof(f3816,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X3,X4,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X4),X5,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X4,X5,sK12(sK1,sK0,sK2))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X4),X5,sK5(sK1,X4,X5,sK12(sK1,sK0,sK2),X3)),X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3805,f3509])).

fof(f3805,plain,(
    ! [X4,X5,X3] :
      ( v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_connsp_2(X3,X4,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X4),X5,sK12(sK1,sK0,sK2)))
      | ~ r1_tmap_1(sK1,X4,X5,sK12(sK1,sK0,sK2))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X4),X5,sK5(sK1,X4,X5,sK12(sK1,sK0,sK2),X3)),X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK1),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f3803,f3517])).

fof(f3517,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2,X3,X6)),X6)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f3514,plain,
    ( ~ v5_pre_topc(sK2,sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4380,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4379,f4294])).

fof(f4294,plain,(
    m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3) ),
    inference(subsumption_resolution,[],[f4293,f3507])).

fof(f4293,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4292,f3508])).

fof(f4292,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4291,f3509])).

fof(f4291,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4290,f3504])).

fof(f4290,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4289,f3505])).

fof(f4289,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4288,f3506])).

fof(f4288,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4287,f3510])).

fof(f4287,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4286,f3511])).

fof(f4286,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4285,f3512])).

fof(f4285,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4284,f4184])).

fof(f4284,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4282,f4185])).

fof(f4185,plain,(
    ~ r1_tmap_1(sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f3515,f4183])).

fof(f3515,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f3454])).

fof(f4282,plain,
    ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4275,f3518])).

fof(f3518,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK4(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f4275,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3))
      | m1_connsp_2(sK14(sK1,sK0,sK2,sK3,X0),sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f4274,f3510])).

fof(f4274,plain,(
    ! [X0] :
      ( m1_connsp_2(sK14(sK1,sK0,sK2,sK3,X0),sK1,sK3)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f4273,f3512])).

fof(f4273,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_connsp_2(sK14(sK1,sK0,sK2,sK3,X0),sK1,sK3)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f4271,f4183])).

fof(f4271,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_connsp_2(sK14(sK1,sK0,sK2,sK3,X0),sK1,sK3)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(resolution,[],[f4236,f3511])).

fof(f4236,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | m1_connsp_2(sK14(sK1,sK0,X0,sK3,X1),sK1,sK3)
      | ~ v1_funct_1(X0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)) ) ),
    inference(subsumption_resolution,[],[f4235,f3504])).

fof(f4235,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK14(sK1,sK0,X0,sK3,X1),sK1,sK3)
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4233,f3506])).

fof(f4233,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK14(sK1,sK0,X0,sK3,X1),sK1,sK3)
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f4218,f3505])).

fof(f4218,plain,(
    ! [X21,X22,X20] :
      ( ~ v2_pre_topc(X21)
      | m1_connsp_2(sK14(sK1,X21,X22,sK3,X20),sK1,sK3)
      | ~ v5_pre_topc(X22,sK1,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X21))))
      | ~ v1_funct_2(X22,u1_struct_0(sK1),u1_struct_0(X21))
      | ~ v1_funct_1(X22)
      | ~ l1_pre_topc(X21)
      | ~ m1_connsp_2(X20,X21,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X21),X22,sK3))
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f4217,f3507])).

fof(f4217,plain,(
    ! [X21,X22,X20] :
      ( ~ m1_connsp_2(X20,X21,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X21),X22,sK3))
      | m1_connsp_2(sK14(sK1,X21,X22,sK3,X20),sK1,sK3)
      | ~ v5_pre_topc(X22,sK1,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X21))))
      | ~ v1_funct_2(X22,u1_struct_0(sK1),u1_struct_0(X21))
      | ~ v1_funct_1(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4216,f3508])).

fof(f4216,plain,(
    ! [X21,X22,X20] :
      ( ~ m1_connsp_2(X20,X21,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X21),X22,sK3))
      | m1_connsp_2(sK14(sK1,X21,X22,sK3,X20),sK1,sK3)
      | ~ v5_pre_topc(X22,sK1,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X21))))
      | ~ v1_funct_2(X22,u1_struct_0(sK1),u1_struct_0(X21))
      | ~ v1_funct_1(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4193,f3509])).

fof(f4193,plain,(
    ! [X21,X22,X20] :
      ( ~ m1_connsp_2(X20,X21,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X21),X22,sK3))
      | m1_connsp_2(sK14(sK1,X21,X22,sK3,X20),sK1,sK3)
      | ~ v5_pre_topc(X22,sK1,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X21))))
      | ~ v1_funct_2(X22,u1_struct_0(sK1),u1_struct_0(X21))
      | ~ v1_funct_1(X22)
      | ~ l1_pre_topc(X21)
      | ~ v2_pre_topc(X21)
      | v2_struct_0(X21)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4184,f3548])).

fof(f3548,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | m1_connsp_2(sK14(X0,X1,X2,X6,X7),X0,X6)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3487])).

fof(f4379,plain,
    ( ~ m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4359,f4185])).

fof(f4359,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ m1_connsp_2(sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4341,f3519])).

fof(f3519,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK4(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_connsp_2(X5,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f4341,plain,(
    r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4340,f3507])).

fof(f4340,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4339,f3508])).

fof(f4339,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4338,f3509])).

fof(f4338,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4337,f3504])).

fof(f4337,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4336,f3505])).

fof(f4336,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4335,f3506])).

fof(f4335,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4334,f3510])).

fof(f4334,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4333,f3511])).

fof(f4333,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4332,f3512])).

fof(f4332,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4331,f4184])).

fof(f4331,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f4329,f4185])).

fof(f4329,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,sK4(sK1,sK0,sK2,sK3))),sK4(sK1,sK0,sK2,sK3))
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f4316,f3518])).

fof(f4316,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,X0)),X0) ) ),
    inference(subsumption_resolution,[],[f4315,f3510])).

fof(f4315,plain,(
    ! [X0] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,X0)),X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f4314,f3512])).

fof(f4314,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,X0)),X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f4312,f4183])).

fof(f4312,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK1,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK14(sK1,sK0,sK2,sK3,X0)),X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_connsp_2(X0,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) ) ),
    inference(resolution,[],[f4255,f3511])).

fof(f4255,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK14(sK1,sK0,X0,sK3,X1)),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)) ) ),
    inference(subsumption_resolution,[],[f4254,f3504])).

fof(f4254,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK14(sK1,sK0,X0,sK3,X1)),X1)
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4252,f3506])).

fof(f4252,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK14(sK1,sK0,X0,sK3,X1)),X1)
      | ~ v5_pre_topc(X0,sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_connsp_2(X1,sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f4221,f3505])).

fof(f4221,plain,(
    ! [X24,X23,X25] :
      ( ~ v2_pre_topc(X24)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X24),X25,sK14(sK1,X24,X25,sK3,X23)),X23)
      | ~ v5_pre_topc(X25,sK1,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X24))))
      | ~ v1_funct_2(X25,u1_struct_0(sK1),u1_struct_0(X24))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(X24)
      | ~ m1_connsp_2(X23,X24,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X24),X25,sK3))
      | v2_struct_0(X24) ) ),
    inference(subsumption_resolution,[],[f4220,f3507])).

fof(f4220,plain,(
    ! [X24,X23,X25] :
      ( ~ m1_connsp_2(X23,X24,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X24),X25,sK3))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X24),X25,sK14(sK1,X24,X25,sK3,X23)),X23)
      | ~ v5_pre_topc(X25,sK1,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X24))))
      | ~ v1_funct_2(X25,u1_struct_0(sK1),u1_struct_0(X24))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(X24)
      | ~ v2_pre_topc(X24)
      | v2_struct_0(X24)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4219,f3508])).

fof(f4219,plain,(
    ! [X24,X23,X25] :
      ( ~ m1_connsp_2(X23,X24,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X24),X25,sK3))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X24),X25,sK14(sK1,X24,X25,sK3,X23)),X23)
      | ~ v5_pre_topc(X25,sK1,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X24))))
      | ~ v1_funct_2(X25,u1_struct_0(sK1),u1_struct_0(X24))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(X24)
      | ~ v2_pre_topc(X24)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f4194,f3509])).

fof(f4194,plain,(
    ! [X24,X23,X25] :
      ( ~ m1_connsp_2(X23,X24,k3_funct_2(u1_struct_0(sK1),u1_struct_0(X24),X25,sK3))
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X24),X25,sK14(sK1,X24,X25,sK3,X23)),X23)
      | ~ v5_pre_topc(X25,sK1,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X24))))
      | ~ v1_funct_2(X25,u1_struct_0(sK1),u1_struct_0(X24))
      | ~ v1_funct_1(X25)
      | ~ l1_pre_topc(X24)
      | ~ v2_pre_topc(X24)
      | v2_struct_0(X24)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f4184,f3549])).

fof(f3549,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK14(X0,X1,X2,X6,X7)),X7)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3487])).
%------------------------------------------------------------------------------
