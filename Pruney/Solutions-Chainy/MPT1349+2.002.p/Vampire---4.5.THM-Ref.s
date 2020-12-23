%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  284 (1660 expanded)
%              Number of leaves         :   33 ( 594 expanded)
%              Depth                    :   29
%              Number of atoms          : 1666 (25606 expanded)
%              Number of equality atoms :  152 (7145 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f126,f130,f131,f132,f133,f177,f212,f215,f218,f248,f286,f305,f310,f320,f338,f342,f346,f360,f366,f461,f526,f544,f550,f563])).

fof(f563,plain,
    ( ~ spl7_1
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl7_1
    | spl7_8 ),
    inference(subsumption_resolution,[],[f561,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_funct_1(sK2)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | ~ v3_tops_2(sK2,sK0,sK1) )
    & ( ( ! [X4] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
      | v3_tops_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | v3_tops_2(X2,X0,X1) )
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
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
                | ~ v3_tops_2(X2,sK0,X1) )
              & ( ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
                | v3_tops_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
              | ~ v3_tops_2(X2,sK0,X1) )
            & ( ( ! [X4] :
                    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
              | v3_tops_2(X2,sK0,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_funct_1(X2)
            | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
            | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
            | ~ v3_tops_2(X2,sK0,sK1) )
          & ( ( ! [X4] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
            | v3_tops_2(X2,sK0,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_funct_1(X2)
          | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1)
          | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          | ~ v3_tops_2(X2,sK0,sK1) )
        & ( ( ! [X4] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) )
          | v3_tops_2(X2,sK0,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_funct_1(sK2)
        | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        | ~ v3_tops_2(sK2,sK0,sK1) )
      & ( ( ! [X4] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) )
        | v3_tops_2(sK2,sK0,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

% (24406)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).

fof(f561,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | spl7_8 ),
    inference(subsumption_resolution,[],[f560,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f560,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | spl7_8 ),
    inference(subsumption_resolution,[],[f559,f103])).

fof(f103,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_1
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f559,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f558,f63])).

fof(f63,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f558,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f557,f64])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f557,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_8 ),
    inference(resolution,[],[f172,f153])).

fof(f153,plain,(
    ! [X8,X9] :
      ( v5_pre_topc(sK2,X8,X9)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
      | ~ v1_funct_2(sK2,u1_struct_0(X8),u1_struct_0(X9))
      | ~ v3_tops_2(sK2,X8,X9)
      | ~ l1_pre_topc(X9)
      | ~ l1_pre_topc(X8) ) ),
    inference(resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f172,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_8
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f550,plain,
    ( spl7_2
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f549,f102,f106])).

fof(f106,plain,
    ( spl7_2
  <=> k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f549,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f548,f58])).

fof(f548,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f547,f61])).

fof(f547,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f546,f63])).

fof(f546,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f351,f64])).

fof(f351,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f103,f151])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ v3_tops_2(sK2,X4,X5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X5))
      | k1_relset_1(u1_struct_0(X4),u1_struct_0(X5),sK2) = k2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f62,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f544,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f542,f125])).

fof(f125,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f542,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_5
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f529])).

fof(f529,plain,
    ( k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_5
    | ~ spl7_7 ),
    inference(superposition,[],[f120,f129])).

fof(f129,plain,
    ( ! [X4] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_7
  <=> ! [X4] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f120,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_5
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f526,plain,
    ( spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f525,f279,f275,f210,f174,f170,f128])).

fof(f174,plain,
    ( spl7_9
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f210,plain,
    ( spl7_14
  <=> ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f275,plain,
    ( spl7_17
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f279,plain,
    ( spl7_18
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f525,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)) )
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f522,f456])).

fof(f456,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f452,f58])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(resolution,[],[f447,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f447,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0))) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(superposition,[],[f444,f211])).

fof(f211,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f444,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(superposition,[],[f439,f211])).

fof(f439,plain,
    ( ! [X1] :
        ( r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f438,f220])).

fof(f220,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f219,f63])).

fof(f219,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f149,f64])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,sK2)) ) ),
    inference(resolution,[],[f62,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f438,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f437,f276])).

fof(f276,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f437,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f416,f280])).

fof(f280,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f279])).

fof(f416,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f388,f175])).

fof(f175,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f388,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK1,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X2)
      | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,X3)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f386,f61])).

fof(f386,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(X2,sK1,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X2)
      | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,X3)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3)))
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f135,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X2)
      | ~ v5_pre_topc(X1,X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f134,f58])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_pre_topc(X1,X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK0)
      | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f57,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f522,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))
        | ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f519,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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

fof(f519,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f518,f62])).

fof(f518,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f517,f63])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f514,f64])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f512,f171])).

fof(f171,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f170])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,k2_pre_topc(sK0,X1)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f510,f58])).

fof(f510,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,k2_pre_topc(sK0,X1)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f146,f57])).

fof(f146,plain,(
    ! [X12,X13,X11] :
      ( ~ v2_pre_topc(X12)
      | ~ v5_pre_topc(X13,X12,sK1)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1))
      | ~ v1_funct_1(X13)
      | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11)))
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) ) ),
    inference(subsumption_resolution,[],[f145,f60])).

fof(f145,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ v5_pre_topc(X13,X12,sK1)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1))
      | ~ v1_funct_1(X13)
      | ~ v2_pre_topc(sK1)
      | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11)))
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12) ) ),
    inference(subsumption_resolution,[],[f141,f61])).

fof(f141,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ v5_pre_topc(X13,X12,sK1)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1))))
      | ~ v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1))
      | ~ v1_funct_1(X13)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11)))
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12) ) ),
    inference(resolution,[],[f59,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f461,plain,
    ( spl7_3
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f460,f102,f110])).

fof(f110,plain,
    ( spl7_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f460,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f459,f58])).

fof(f459,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f458,f61])).

fof(f458,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f457,f63])).

fof(f457,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f350,f64])).

fof(f350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f103,f152])).

fof(f152,plain,(
    ! [X6,X7] :
      ( ~ v3_tops_2(sK2,X6,X7)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X7))
      | k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),sK2) = k2_struct_0(X7)
      | ~ l1_pre_topc(X7)
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f62,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f366,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl7_1
    | spl7_4 ),
    inference(subsumption_resolution,[],[f364,f58])).

fof(f364,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | spl7_4 ),
    inference(subsumption_resolution,[],[f363,f61])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | spl7_4 ),
    inference(subsumption_resolution,[],[f362,f103])).

fof(f362,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f361,f64])).

fof(f361,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_4 ),
    inference(resolution,[],[f348,f63])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v3_tops_2(sK2,X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | spl7_4 ),
    inference(subsumption_resolution,[],[f347,f62])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ v3_tops_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | spl7_4 ),
    inference(resolution,[],[f116,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f360,plain,
    ( spl7_9
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f359,f102,f174])).

fof(f359,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f358,f58])).

fof(f358,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f353,f61])).

fof(f353,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f352,f63])).

fof(f352,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f349,f64])).

fof(f349,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f103,f154])).

fof(f154,plain,(
    ! [X10,X11] :
      ( ~ v3_tops_2(sK2,X10,X11)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
      | ~ v1_funct_2(sK2,u1_struct_0(X10),u1_struct_0(X11))
      | v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),sK2),X11,X10)
      | ~ l1_pre_topc(X11)
      | ~ l1_pre_topc(X10) ) ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f346,plain,
    ( ~ spl7_7
    | ~ spl7_16
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_16
    | spl7_22 ),
    inference(subsumption_resolution,[],[f344,f272])).

fof(f272,plain,
    ( m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl7_16
  <=> m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f344,plain,
    ( ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_22 ),
    inference(subsumption_resolution,[],[f343,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f343,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_22 ),
    inference(superposition,[],[f337,f129])).

fof(f337,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl7_22
  <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f342,plain,
    ( ~ spl7_16
    | spl7_20 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl7_16
    | spl7_20 ),
    inference(subsumption_resolution,[],[f340,f58])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_16
    | spl7_20 ),
    inference(subsumption_resolution,[],[f339,f272])).

fof(f339,plain,
    ( ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl7_20 ),
    inference(resolution,[],[f296,f75])).

fof(f296,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl7_20
  <=> m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f338,plain,
    ( ~ spl7_20
    | ~ spl7_22
    | ~ spl7_14
    | spl7_19 ),
    inference(avatar_split_clause,[],[f333,f283,f210,f335,f294])).

fof(f283,plain,
    ( spl7_19
  <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f333,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_14
    | spl7_19 ),
    inference(superposition,[],[f285,f211])).

fof(f285,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f283])).

fof(f320,plain,
    ( spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f318,f60])).

fof(f318,plain,
    ( ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f317,f61])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f316,f57])).

fof(f316,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f315,f58])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f314,f220])).

fof(f314,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f313,f276])).

fof(f313,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f312,f280])).

fof(f312,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_9
    | spl7_16 ),
    inference(subsumption_resolution,[],[f311,f176])).

fof(f176,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f311,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl7_16 ),
    inference(resolution,[],[f273,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f273,plain,
    ( ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f271])).

fof(f310,plain,(
    spl7_18 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl7_18 ),
    inference(subsumption_resolution,[],[f308,f62])).

fof(f308,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f307,f63])).

fof(f307,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f306,f64])).

fof(f306,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | spl7_18 ),
    inference(resolution,[],[f281,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f281,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f279])).

fof(f305,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl7_17 ),
    inference(subsumption_resolution,[],[f303,f64])).

fof(f303,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl7_17 ),
    inference(subsumption_resolution,[],[f302,f63])).

fof(f302,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl7_17 ),
    inference(resolution,[],[f277,f150])).

fof(f150,plain,(
    ! [X2,X3] :
      ( v1_funct_2(k2_tops_2(X2,X3,sK2),X3,X2)
      | ~ v1_funct_2(sK2,X2,X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f62,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f277,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f286,plain,
    ( ~ spl7_16
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | spl7_9
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f269,f210,f174,f283,f279,f275,f271])).

fof(f269,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f268,f60])).

fof(f268,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f267,f61])).

fof(f267,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f266,f57])).

fof(f266,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f265,f58])).

fof(f265,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f264,f220])).

fof(f264,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f262,f176])).

fof(f262,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_14 ),
    inference(superposition,[],[f91,f211])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f248,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f246,f57])).

fof(f246,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f245,f58])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f244,f59])).

fof(f244,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f243,f60])).

fof(f243,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f242,f61])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f241,f62])).

fof(f241,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f240,f63])).

fof(f240,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f239,f64])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f238,f172])).

fof(f238,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | spl7_8 ),
    inference(resolution,[],[f237,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f237,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f236,f57])).

fof(f236,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f235,f58])).

fof(f235,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f234,f59])).

fof(f234,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f233,f60])).

fof(f233,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f232,f61])).

fof(f232,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f231,f62])).

fof(f231,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f230,f63])).

fof(f230,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f229,f64])).

fof(f229,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f228,f172])).

fof(f228,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f227,f100])).

fof(f227,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7 ),
    inference(superposition,[],[f73,f129])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f218,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f216,f58])).

fof(f216,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_12 ),
    inference(resolution,[],[f204,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f204,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f215,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl7_13 ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_13 ),
    inference(resolution,[],[f208,f98])).

fof(f208,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl7_13
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f212,plain,
    ( ~ spl7_12
    | ~ spl7_13
    | spl7_14
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f200,f114,f110,f210,f206,f202])).

fof(f200,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f199,f62])).

fof(f199,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f198,f63])).

fof(f198,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f197,f64])).

fof(f197,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f158,f115])).

fof(f115,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( ! [X0] :
        ( k2_struct_0(sK1) != k2_struct_0(sK1)
        | ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f74,f111])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f177,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f168,f114,f110,f106,f102,f174,f170])).

fof(f168,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f167,f58])).

fof(f167,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f166,f61])).

fof(f166,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f165,f62])).

fof(f165,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f164,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f163,f64])).

fof(f163,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f162,f107])).

fof(f107,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f162,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f161,f104])).

fof(f104,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f161,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f160,f115])).

fof(f160,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(superposition,[],[f87,f111])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
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
    inference(cnf_transformation,[],[f50])).

fof(f133,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f65,f106,f102])).

fof(f65,plain,
    ( k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f66,f110,f102])).

fof(f66,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f67,f114,f102])).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f130,plain,
    ( spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f68,f128,f102])).

fof(f68,plain,(
    ! [X4] :
      ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f69,f123,f114,f110,f106,f102])).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f70,f118,f114,f110,f106,f102])).

fof(f70,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (24398)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (24402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (24410)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (24411)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (24420)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (24403)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (24405)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (24412)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (24418)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (24404)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (24407)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (24421)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (24400)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (24409)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (24408)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (24413)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (24401)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (24417)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (24415)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (24419)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (24399)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24404)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f564,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f121,f126,f130,f131,f132,f133,f177,f212,f215,f218,f248,f286,f305,f310,f320,f338,f342,f346,f360,f366,f461,f526,f544,f550,f563])).
% 0.21/0.53  fof(f563,plain,(
% 0.21/0.53    ~spl7_1 | spl7_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f562])).
% 0.21/0.53  fof(f562,plain,(
% 0.21/0.53    $false | (~spl7_1 | spl7_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f561,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ((((k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v3_tops_2(sK2,sK0,sK1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v3_tops_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37,f36,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0) | ~v3_tops_2(X2,sK0,X1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0)) | v3_tops_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0) | ~v3_tops_2(X2,sK0,X1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0)) | v3_tops_2(X2,sK0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) | ~v3_tops_2(X2,sK0,sK1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | v3_tops_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) != k2_struct_0(sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) | ~v3_tops_2(X2,sK0,sK1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | v3_tops_2(X2,sK0,sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v3_tops_2(sK2,sK0,sK1)) & ((! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v3_tops_2(sK2,sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) != k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  % (24406)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).
% 0.21/0.54  fof(f561,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | (~spl7_1 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f560,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    l1_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f560,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (~spl7_1 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f559,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    v3_tops_2(sK2,sK0,sK1) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl7_1 <=> v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f559,plain,(
% 0.21/0.54    ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | spl7_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f558,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f558,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | spl7_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f557,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f557,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | spl7_8),
% 0.21/0.54    inference(resolution,[],[f172,f153])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X8,X9] : (v5_pre_topc(sK2,X8,X9) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))) | ~v1_funct_2(sK2,u1_struct_0(X8),u1_struct_0(X9)) | ~v3_tops_2(sK2,X8,X9) | ~l1_pre_topc(X9) | ~l1_pre_topc(X8)) )),
% 0.21/0.54    inference(resolution,[],[f62,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~v5_pre_topc(sK2,sK0,sK1) | spl7_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f170])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl7_8 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.54  fof(f550,plain,(
% 0.21/0.54    spl7_2 | ~spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f549,f102,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl7_2 <=> k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f549,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f548,f58])).
% 0.21/0.54  fof(f548,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f547,f61])).
% 0.21/0.54  fof(f547,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f546,f63])).
% 0.21/0.54  fof(f546,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f351,f64])).
% 0.21/0.54  fof(f351,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(resolution,[],[f103,f151])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~v3_tops_2(sK2,X4,X5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X5)) | k1_relset_1(u1_struct_0(X4),u1_struct_0(X5),sK2) = k2_struct_0(X4) | ~l1_pre_topc(X5) | ~l1_pre_topc(X4)) )),
% 0.21/0.54    inference(resolution,[],[f62,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    spl7_5 | ~spl7_6 | ~spl7_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f543])).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    $false | (spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f542,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.54  fof(f542,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_5 | ~spl7_7)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f529])).
% 0.21/0.54  fof(f529,plain,(
% 0.21/0.54    k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_5 | ~spl7_7)),
% 0.21/0.54    inference(superposition,[],[f120,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl7_7 <=> ! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl7_5 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f526,plain,(
% 0.21/0.54    spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f525,f279,f275,f210,f174,f170,f128])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl7_9 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    spl7_14 <=> ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    spl7_17 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    spl7_18 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f525,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1))) ) | (~spl7_8 | ~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f522,f456])).
% 0.21/0.54  fof(f456,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f452,f58])).
% 0.21/0.54  fof(f452,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0))) | ~l1_pre_topc(sK0)) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f451])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(resolution,[],[f447,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.54  fof(f447,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)))) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(superposition,[],[f444,f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f210])).
% 0.21/0.54  fof(f444,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f442])).
% 0.21/0.54  fof(f442,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_14 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(superposition,[],[f439,f211])).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f438,f220])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.54    inference(subsumption_resolution,[],[f219,f63])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.54    inference(resolution,[],[f149,f64])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f62,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.54  fof(f438,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f437,f276])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl7_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f275])).
% 0.21/0.54  fof(f437,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_9 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f416,f280])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f279])).
% 0.21/0.54  fof(f416,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X1)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_9),
% 0.21/0.54    inference(resolution,[],[f388,f175])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl7_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f174])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v5_pre_topc(X2,sK1,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X2) | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,X3)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f386,f61])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v5_pre_topc(X2,sK1,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X2) | r1_tarski(k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,X3)),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_pre_topc(sK0,X3))) | ~l1_pre_topc(sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(resolution,[],[f135,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    v2_pre_topc(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X2) | ~v5_pre_topc(X1,X2,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X1) | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) | ~l1_pre_topc(X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f134,f58])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_pre_topc(X1,X2,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) | ~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~l1_pre_topc(sK0) | r1_tarski(k2_pre_topc(X2,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,X0)),k8_relset_1(u1_struct_0(X2),u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.21/0.54    inference(resolution,[],[f57,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~v2_pre_topc(X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(rectify,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f522,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)) | ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1)),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X1)))) ) | ~spl7_8),
% 0.21/0.54    inference(resolution,[],[f519,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f519,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f518,f62])).
% 0.21/0.54  fof(f518,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(sK2) | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f517,f63])).
% 0.21/0.54  fof(f517,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f514,f64])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_8),
% 0.21/0.54    inference(resolution,[],[f512,f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    v5_pre_topc(sK2,sK0,sK1) | ~spl7_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f170])).
% 0.21/0.54  fof(f512,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,k2_pre_topc(sK0,X1)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f510,f58])).
% 0.21/0.54  fof(f510,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v5_pre_topc(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,k2_pre_topc(sK0,X1)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(resolution,[],[f146,f57])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X12,X13,X11] : (~v2_pre_topc(X12) | ~v5_pre_topc(X13,X12,sK1) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1)) | ~v1_funct_1(X13) | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11))) | ~l1_pre_topc(X12) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f60])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X12,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | ~v5_pre_topc(X13,X12,sK1) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1)) | ~v1_funct_1(X13) | ~v2_pre_topc(sK1) | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11))) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f61])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X12,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | ~v5_pre_topc(X13,X12,sK1) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(sK1)))) | ~v1_funct_2(X13,u1_struct_0(X12),u1_struct_0(sK1)) | ~v1_funct_1(X13) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | r1_tarski(k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,k2_pre_topc(X12,X11)),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(X12),u1_struct_0(sK1),X13,X11))) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12)) )),
% 0.21/0.54    inference(resolution,[],[f59,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (v2_struct_0(X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(rectify,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    spl7_3 | ~spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f460,f102,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    spl7_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f459,f58])).
% 0.21/0.54  fof(f459,plain,(
% 0.21/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f458,f61])).
% 0.21/0.54  fof(f458,plain,(
% 0.21/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f457,f63])).
% 0.21/0.54  fof(f457,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f350,f64])).
% 0.21/0.54  fof(f350,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(resolution,[],[f103,f152])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X6,X7] : (~v3_tops_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(sK2,u1_struct_0(X6),u1_struct_0(X7)) | k2_relset_1(u1_struct_0(X6),u1_struct_0(X7),sK2) = k2_struct_0(X7) | ~l1_pre_topc(X7) | ~l1_pre_topc(X6)) )),
% 0.21/0.54    inference(resolution,[],[f62,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~spl7_1 | spl7_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f365])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    $false | (~spl7_1 | spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f364,f58])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | (~spl7_1 | spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f363,f61])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (~spl7_1 | spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f362,f103])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | spl7_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f361,f64])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | spl7_4),
% 0.21/0.54    inference(resolution,[],[f348,f63])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_tops_2(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | spl7_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f347,f62])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_tops_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | spl7_4),
% 0.21/0.54    inference(resolution,[],[f116,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ~v2_funct_1(sK2) | spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl7_4 <=> v2_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    spl7_9 | ~spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f359,f102,f174])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f358,f58])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f353,f61])).
% 0.21/0.54  fof(f353,plain,(
% 0.21/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f352,f63])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f349,f64])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.21/0.54    inference(resolution,[],[f103,f154])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X10,X11] : (~v3_tops_2(sK2,X10,X11) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11)))) | ~v1_funct_2(sK2,u1_struct_0(X10),u1_struct_0(X11)) | v5_pre_topc(k2_tops_2(u1_struct_0(X10),u1_struct_0(X11),sK2),X11,X10) | ~l1_pre_topc(X11) | ~l1_pre_topc(X10)) )),
% 0.21/0.54    inference(resolution,[],[f62,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f346,plain,(
% 0.21/0.54    ~spl7_7 | ~spl7_16 | spl7_22),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f345])).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    $false | (~spl7_7 | ~spl7_16 | spl7_22)),
% 0.21/0.54    inference(subsumption_resolution,[],[f344,f272])).
% 0.21/0.54  fof(f272,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl7_16 <=> m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_22)),
% 0.21/0.54    inference(subsumption_resolution,[],[f343,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f56])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_22)),
% 0.21/0.54    inference(superposition,[],[f337,f129])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | spl7_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f335])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    spl7_22 <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    ~spl7_16 | spl7_20),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f341])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    $false | (~spl7_16 | spl7_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f340,f58])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | (~spl7_16 | spl7_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f339,f272])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl7_20),
% 0.21/0.54    inference(resolution,[],[f296,f75])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    ~m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f294])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    spl7_20 <=> m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    ~spl7_20 | ~spl7_22 | ~spl7_14 | spl7_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f333,f283,f210,f335,f294])).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    spl7_19 <=> r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_14 | spl7_19)),
% 0.21/0.54    inference(superposition,[],[f285,f211])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | spl7_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f283])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f319])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    $false | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f318,f60])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f317,f61])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f316,f57])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f315,f58])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f314,f220])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_17 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f313,f276])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16 | ~spl7_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f312,f280])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (spl7_9 | spl7_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f311,f176])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl7_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f174])).
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl7_16),
% 0.21/0.54    inference(resolution,[],[f273,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f273,plain,(
% 0.21/0.54    ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f271])).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    spl7_18),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    $false | spl7_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f308,f62])).
% 0.21/0.54  fof(f308,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | spl7_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f307,f63])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | spl7_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f306,f64])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | spl7_18),
% 0.21/0.54    inference(resolution,[],[f281,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f279])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    spl7_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f304])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    $false | spl7_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f303,f64])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl7_17),
% 0.21/0.54    inference(subsumption_resolution,[],[f302,f63])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl7_17),
% 0.21/0.54    inference(resolution,[],[f277,f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X2,X3] : (v1_funct_2(k2_tops_2(X2,X3,sK2),X3,X2) | ~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.21/0.54    inference(resolution,[],[f62,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl7_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f275])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    ~spl7_16 | ~spl7_17 | ~spl7_18 | ~spl7_19 | spl7_9 | ~spl7_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f269,f210,f174,f283,f279,f275,f271])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f60])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f61])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f266,f57])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f265,f58])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f264,f220])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f262,f176])).
% 0.21/0.54  fof(f262,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~m1_subset_1(sK6(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_14),
% 0.21/0.54    inference(superposition,[],[f91,f211])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ~spl7_7 | spl7_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    $false | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f246,f57])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f245,f58])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f244,f59])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f243,f60])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f242,f61])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f241,f62])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f240,f63])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f64])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f238,f172])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(resolution,[],[f237,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f236,f57])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f235,f58])).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f234,f59])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f233,f60])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f61])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f231,f62])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f230,f63])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f229,f64])).
% 0.21/0.54  fof(f229,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_7 | spl7_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f228,f172])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f227,f100])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    ~r1_tarski(k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)))) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_7),
% 0.21/0.54    inference(superposition,[],[f73,f129])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK4(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    spl7_12),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f217])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    $false | spl7_12),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f58])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | spl7_12),
% 0.21/0.54    inference(resolution,[],[f204,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | spl7_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f202])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    spl7_12 <=> l1_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    spl7_13),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    $false | spl7_13),
% 0.21/0.54    inference(subsumption_resolution,[],[f213,f61])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ~l1_pre_topc(sK1) | spl7_13),
% 0.21/0.54    inference(resolution,[],[f208,f98])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    ~l1_struct_0(sK1) | spl7_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f206])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl7_13 <=> l1_struct_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ~spl7_12 | ~spl7_13 | spl7_14 | ~spl7_3 | ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f200,f114,f110,f210,f206,f202])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f199,f62])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f198,f63])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f197,f64])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f158,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    v2_funct_1(sK2) | ~spl7_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | ~spl7_3),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(sK0)) ) | ~spl7_3),
% 0.21/0.54    inference(superposition,[],[f74,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f110])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~spl7_8 | ~spl7_9 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f168,f114,f110,f106,f102,f174,f170])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f167,f58])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f166,f61])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f165,f62])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f164,f63])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f163,f64])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f106])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f161,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~v3_tops_2(sK2,sK0,sK1) | spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | v3_tops_2(sK2,sK0,sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (~spl7_3 | ~spl7_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f115])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_funct_1(sK2) | v3_tops_2(sK2,sK0,sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_3),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f155])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v2_funct_1(sK2) | v3_tops_2(sK2,sK0,sK1) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~spl7_3),
% 0.21/0.54    inference(superposition,[],[f87,f111])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | v3_tops_2(X2,X0,X1) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f65,f106,f102])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl7_1 | spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f66,f110,f102])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl7_1 | spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f67,f114,f102])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    v2_funct_1(sK2) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl7_1 | spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f68,f128,f102])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X4] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X4)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f69,f123,f114,f110,f106,f102])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f70,f118,f114,f110,f106,f102])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24404)------------------------------
% 0.21/0.54  % (24404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24404)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24404)Memory used [KB]: 11129
% 0.21/0.54  % (24404)Time elapsed: 0.083 s
% 0.21/0.54  % (24404)------------------------------
% 0.21/0.54  % (24404)------------------------------
% 0.21/0.54  % (24422)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (24397)Success in time 0.193 s
%------------------------------------------------------------------------------
