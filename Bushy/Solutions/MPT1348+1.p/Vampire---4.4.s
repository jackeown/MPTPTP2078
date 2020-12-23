%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t73_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:43 EDT 2019

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  298 (2757 expanded)
%              Number of leaves         :   40 ( 953 expanded)
%              Depth                    :   28
%              Number of atoms          : 1564 (42764 expanded)
%              Number of equality atoms :  189 (12298 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11002,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f200,f207,f211,f212,f279,f292,f485,f510,f529,f536,f616,f1064,f1156,f10259,f10265,f10280,f10294,f10418,f10998,f11001])).

fof(f11001,plain,
    ( ~ spl10_0
    | spl10_87 ),
    inference(avatar_contradiction_clause,[],[f11000])).

fof(f11000,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f6744,f172])).

fof(f172,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl10_0
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f6744,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f6743,f110])).

fof(f110,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( ( ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_funct_1(sK2)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
      | ~ v3_tops_2(sK2,sK0,sK1) )
    & ( ( ! [X4] :
            ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) )
      | v3_tops_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f83,f87,f86,f85,f84])).

fof(f84,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
                | ~ v3_tops_2(X2,sK0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
                | v3_tops_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(sK1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK1) )
            & ( ( ! [X4] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_pre_topc(sK1,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ v2_funct_1(X2)
            | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
            | ~ v3_tops_2(X2,X0,X1) )
          & ( ( ! [X4] :
                  ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
            | v3_tops_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X1,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v2_funct_1(sK2)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
          | ~ v3_tops_2(sK2,X0,X1) )
        & ( ( ! [X4] :
                ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_pre_topc(X1,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & v2_funct_1(sK2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X0) )
          | v3_tops_2(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                       => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',t73_tops_2)).

fof(f6743,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f6742,f112])).

fof(f112,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f6742,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f6741,f113])).

fof(f113,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f6741,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f6740,f114])).

fof(f114,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

fof(f6740,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f1357,f115])).

fof(f115,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

fof(f1357,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_87 ),
    inference(resolution,[],[f733,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',d5_tops_2)).

fof(f733,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl10_87
  <=> ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f10998,plain,
    ( spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(avatar_contradiction_clause,[],[f10997])).

fof(f10997,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(subsumption_resolution,[],[f10996,f206])).

fof(f206,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl10_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f10996,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(subsumption_resolution,[],[f10993,f664])).

fof(f664,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK3)) != k10_relat_1(sK2,k2_pre_topc(sK1,sK3))
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f659,f225])).

fof(f225,plain,(
    ! [X2] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k10_relat_1(sK2,X2) ),
    inference(resolution,[],[f115,f163])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',redefinition_k8_relset_1)).

fof(f659,plain,
    ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k10_relat_1(sK2,k2_pre_topc(sK1,sK3))
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f225,f199])).

fof(f199,plain,
    ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_9
  <=> k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f10993,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK3)) = k10_relat_1(sK2,k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(resolution,[],[f10983,f10555])).

fof(f10555,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k10_relat_1(sK2,k2_pre_topc(sK1,X1)),k2_pre_topc(sK0,k10_relat_1(sK2,X1)))
        | k2_pre_topc(sK0,k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_pre_topc(sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_22 ),
    inference(resolution,[],[f6776,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',d10_xboole_0)).

fof(f6776,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,k2_pre_topc(sK1,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f6775,f225])).

fof(f6775,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k10_relat_1(sK2,k2_pre_topc(sK1,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f278,f225])).

fof(f278,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1))) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl10_22
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f10983,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK0,k10_relat_1(sK2,sK3)))
    | ~ spl10_10
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(forward_demodulation,[],[f10982,f7204])).

fof(f7204,plain,
    ( k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) = k10_relat_1(sK2,sK3)
    | ~ spl10_10
    | ~ spl10_54 ),
    inference(resolution,[],[f1766,f206])).

fof(f1766,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) = k10_relat_1(sK2,X0) )
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f1765,f225])).

fof(f1765,plain,
    ( ! [X0] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f451,f808])).

fof(f808,plain,(
    ! [X3] : k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) = k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) ),
    inference(resolution,[],[f296,f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',redefinition_k7_relset_1)).

fof(f296,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f295,f113])).

fof(f295,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f228,f114])).

fof(f228,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f115,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',dt_k2_tops_2)).

fof(f451,plain,
    ( ! [X0] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl10_54
  <=> ! [X0] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f10982,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)))
    | ~ spl10_10
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(subsumption_resolution,[],[f10973,f206])).

fof(f10973,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_pre_topc(sK1,sK3)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_10
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(superposition,[],[f10279,f8120])).

fof(f8120,plain,
    ( k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK3)) = k10_relat_1(sK2,k2_pre_topc(sK1,sK3))
    | ~ spl10_10
    | ~ spl10_54 ),
    inference(resolution,[],[f7208,f206])).

fof(f7208,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X4)) = k10_relat_1(sK2,k2_pre_topc(sK1,X4)) )
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f7198,f112])).

fof(f7198,plain,
    ( ! [X4] :
        ( k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X4)) = k10_relat_1(sK2,k2_pre_topc(sK1,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl10_54 ),
    inference(resolution,[],[f1766,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',dt_k2_pre_topc)).

fof(f10279,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_696 ),
    inference(avatar_component_clause,[],[f10278])).

fof(f10278,plain,
    ( spl10_696
  <=> ! [X0] :
        ( r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_696])])).

fof(f10418,plain,
    ( ~ spl10_12
    | ~ spl10_24
    | spl10_131 ),
    inference(avatar_contradiction_clause,[],[f10417])).

fof(f10417,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_24
    | ~ spl10_131 ),
    inference(subsumption_resolution,[],[f10409,f167])).

fof(f167,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f102])).

fof(f10409,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))))
    | ~ spl10_12
    | ~ spl10_24
    | ~ spl10_131 ),
    inference(backward_demodulation,[],[f10347,f1054])).

fof(f1054,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | ~ spl10_131 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1053,plain,
    ( spl10_131
  <=> ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_131])])).

fof(f10347,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2)))
    | ~ spl10_12
    | ~ spl10_24 ),
    inference(resolution,[],[f291,f699])).

fof(f699,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,k10_relat_1(sK2,X4)) = k10_relat_1(sK2,k2_pre_topc(sK1,X4)) )
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f698,f225])).

fof(f698,plain,
    ( ! [X4] :
        ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) = k10_relat_1(sK2,k2_pre_topc(sK1,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f210,f225])).

fof(f210,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4)) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl10_12
  <=> ! [X4] :
        ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f291,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl10_24
  <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f10294,plain,
    ( spl10_0
    | ~ spl10_17
    | ~ spl10_87
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f10293,f189,f183,f177,f732,f251,f171])).

fof(f251,plain,
    ( spl10_17
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f177,plain,
    ( spl10_2
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f183,plain,
    ( spl10_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f189,plain,
    ( spl10_6
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f10293,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10292,f110])).

fof(f10292,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10291,f112])).

fof(f10291,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10290,f113])).

fof(f10290,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10289,f114])).

fof(f10289,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f10288,f115])).

fof(f10288,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1332,f178])).

fof(f178,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1332,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f508,f190])).

fof(f190,plain,
    ( v2_funct_1(sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f508,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(superposition,[],[f131,f184])).

fof(f184,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f183])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v3_tops_2(X2,X0,X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f10280,plain,
    ( ~ spl10_87
    | spl10_696
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f10276,f821,f10278,f732])).

fof(f821,plain,
    ( spl10_88
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f10276,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) )
    | ~ spl10_88 ),
    inference(forward_demodulation,[],[f10275,f808])).

fof(f10275,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) )
    | ~ spl10_88 ),
    inference(forward_demodulation,[],[f10274,f808])).

fof(f10274,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
        | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0))) )
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1185,f822])).

fof(f822,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f821])).

fof(f1185,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1184,f111])).

fof(f111,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f1184,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f1183,f112])).

fof(f1183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f1182,f108])).

fof(f108,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f1182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f1181,f109])).

fof(f109,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f1181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f1180,f110])).

fof(f1180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f803,f294])).

fof(f294,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f293,f113])).

fof(f293,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f227,f114])).

fof(f227,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f115,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f803,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,X0)),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f296,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f92,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',t57_tops_2)).

fof(f10265,plain,
    ( spl10_16
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f10264,f174,f248])).

fof(f248,plain,
    ( spl10_16
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f174,plain,
    ( spl10_1
  <=> ~ v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f10264,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f10263,f110])).

fof(f10263,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f10262,f112])).

fof(f10262,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f10261,f113])).

fof(f10261,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f220,f114])).

fof(f220,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f10259,plain,
    ( ~ spl10_12
    | ~ spl10_54
    | spl10_87
    | ~ spl10_88 ),
    inference(avatar_contradiction_clause,[],[f10258])).

fof(f10258,plain,
    ( $false
    | ~ spl10_12
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f10250,f167])).

fof(f10250,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl10_12
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(backward_demodulation,[],[f10130,f9835])).

fof(f9835,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(forward_demodulation,[],[f1739,f7205])).

fof(f7205,plain,
    ( k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(resolution,[],[f1766,f6779])).

fof(f6779,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f6778,f822])).

fof(f6778,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f1177,f733])).

fof(f1177,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1176,f111])).

fof(f1176,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1175,f112])).

fof(f1175,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1174,f108])).

fof(f1174,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1173,f109])).

fof(f1173,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1172,f110])).

fof(f1172,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f804,f294])).

fof(f804,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f296,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f1739,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(forward_demodulation,[],[f1738,f808])).

fof(f1738,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1737,f111])).

fof(f1737,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1736,f112])).

fof(f1736,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1735,f108])).

fof(f1735,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1734,f109])).

fof(f1734,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1733,f110])).

fof(f1733,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1732,f294])).

fof(f1732,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f1731,f822])).

fof(f1731,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f1730,f296])).

fof(f1730,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f1727,f733])).

fof(f1727,plain,
    ( ~ r1_tarski(k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK0,k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f134,f808])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f10130,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl10_12
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(forward_demodulation,[],[f8121,f7153])).

fof(f7153,plain,
    ( k2_pre_topc(sK0,k10_relat_1(sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl10_12
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(resolution,[],[f6779,f699])).

fof(f8121,plain,
    ( k9_relat_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k10_relat_1(sK2,k2_pre_topc(sK1,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl10_54
    | ~ spl10_87
    | ~ spl10_88 ),
    inference(resolution,[],[f7208,f6779])).

fof(f1156,plain,(
    spl10_89 ),
    inference(avatar_contradiction_clause,[],[f1155])).

fof(f1155,plain,
    ( $false
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f1154,f113])).

fof(f1154,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f1153,f114])).

fof(f1153,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f1152,f115])).

fof(f1152,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl10_89 ),
    inference(resolution,[],[f825,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f825,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl10_89
  <=> ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f1064,plain,
    ( spl10_16
    | ~ spl10_131 ),
    inference(avatar_split_clause,[],[f1063,f1053,f248])).

fof(f1063,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k10_relat_1(sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f1062,f225])).

fof(f1062,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f1061,f109])).

fof(f1061,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1060,f110])).

fof(f1060,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1059,f111])).

fof(f1059,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1058,f112])).

fof(f1058,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1057,f113])).

fof(f1057,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1056,f114])).

fof(f1056,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f660,f115])).

fof(f660,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k10_relat_1(sK2,sK5(sK0,sK1,sK2))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK5(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f137,f225])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f96,f97])).

fof(f97,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK5(X0,X1,X2))))
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',t56_tops_2)).

fof(f616,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f366,f181])).

fof(f181,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_3
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f366,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(global_subsumption,[],[f116,f365])).

fof(f365,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f364,f110])).

fof(f364,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f363,f112])).

fof(f363,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f362,f113])).

fof(f362,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f217,f114])).

fof(f217,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f116,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f536,plain,
    ( ~ spl10_0
    | spl10_7 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f534,f193])).

fof(f193,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl10_7
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f534,plain,
    ( v2_funct_1(sK2)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f533,f110])).

fof(f533,plain,
    ( v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f532,f112])).

fof(f532,plain,
    ( v2_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f531,f113])).

fof(f531,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f530,f114])).

fof(f530,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f219,f172])).

fof(f219,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f529,plain,
    ( spl10_54
    | ~ spl10_7
    | ~ spl10_57 ),
    inference(avatar_split_clause,[],[f528,f456,f192,f450])).

fof(f456,plain,
    ( spl10_57
  <=> k2_struct_0(sK1) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f528,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f527,f215])).

fof(f215,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f110,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',dt_l1_pre_topc)).

fof(f527,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f526,f216])).

fof(f216,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f112,f125])).

fof(f526,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f525,f113])).

fof(f525,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f524,f114])).

fof(f524,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f441,f115])).

fof(f441,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relat_1(sK2)
      | ~ v2_funct_1(sK2)
      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(sK0) ) ),
    inference(superposition,[],[f124,f229])).

fof(f229,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f115,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',redefinition_k2_relset_1)).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v2_funct_1(X2)
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t73_tops_2.p',t68_tops_2)).

fof(f510,plain,
    ( ~ spl10_4
    | spl10_57 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_57 ),
    inference(subsumption_resolution,[],[f503,f457])).

fof(f457,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f456])).

fof(f503,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl10_4 ),
    inference(backward_demodulation,[],[f184,f229])).

fof(f485,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f361,f187])).

fof(f187,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl10_5
  <=> k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f361,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(global_subsumption,[],[f117,f360])).

fof(f360,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f359,f110])).

fof(f359,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f358,f112])).

fof(f358,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f357,f113])).

fof(f357,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f218,f114])).

fof(f218,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f115,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f117,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f292,plain,
    ( spl10_16
    | spl10_24 ),
    inference(avatar_split_clause,[],[f285,f290,f248])).

fof(f285,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f284,f109])).

fof(f284,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f283,f110])).

fof(f283,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f282,f111])).

fof(f282,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f281,f112])).

fof(f281,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f280,f113])).

fof(f280,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f224,f114])).

fof(f224,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f115,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f279,plain,
    ( ~ spl10_17
    | spl10_22 ),
    inference(avatar_split_clause,[],[f275,f277,f251])).

fof(f275,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f274,f109])).

fof(f274,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f110])).

fof(f273,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f272,f111])).

fof(f272,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f271,f112])).

fof(f271,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f113])).

fof(f270,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f223,f114])).

fof(f223,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X1)))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f115,f135])).

fof(f135,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f212,plain,
    ( spl10_0
    | spl10_6 ),
    inference(avatar_split_clause,[],[f118,f189,f171])).

fof(f118,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f211,plain,
    ( spl10_0
    | spl10_12 ),
    inference(avatar_split_clause,[],[f119,f209,f171])).

fof(f119,plain,(
    ! [X4] :
      ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f207,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | spl10_10 ),
    inference(avatar_split_clause,[],[f120,f205,f192,f186,f180,f174])).

fof(f120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f200,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f121,f198,f192,f186,f180,f174])).

fof(f121,plain,
    ( k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK1,sK3))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).
%------------------------------------------------------------------------------
