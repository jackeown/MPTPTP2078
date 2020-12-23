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
% DateTime   : Thu Dec  3 13:09:30 EST 2020

% Result     : Theorem 12.04s
% Output     : Refutation 12.80s
% Verified   : 
% Statistics : Number of formulae       :  581 (4753 expanded)
%              Number of leaves         :   50 (1577 expanded)
%              Depth                    :   31
%              Number of atoms          : 2882 (46606 expanded)
%              Number of equality atoms :  181 (5547 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f206,f207,f339,f392,f620,f636,f642,f652,f697,f707,f761,f793,f817,f821,f845,f1099,f1109,f1135,f1137,f1196,f1297,f1394,f1430,f1557,f1570,f1588,f3908,f3995,f4502,f6267,f6319,f8259,f8324,f8822,f9003,f9245,f9264,f10022,f10300,f10543,f10563,f10608,f11021,f11042,f11313])).

fof(f11313,plain,
    ( spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f11312])).

fof(f11312,plain,
    ( $false
    | spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f11311,f95])).

fof(f95,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f11311,plain,
    ( ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f11310,f96])).

fof(f96,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f11310,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f11309,f10452])).

fof(f10452,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10408,f391])).

fof(f391,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl9_17
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f10408,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(superposition,[],[f100,f10064])).

fof(f10064,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10063,f184])).

fof(f184,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f10063,plain,
    ( sK2 = k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f619,f391])).

fof(f619,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl9_27
  <=> k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f100,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

fof(f11309,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f11308,f10633])).

fof(f10633,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f635,f10064])).

fof(f635,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl9_30
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f11308,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f11305,f11068])).

fof(f11068,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_1
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f201,f10064])).

fof(f201,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl9_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f11305,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(resolution,[],[f9506,f11266])).

fof(f11266,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f11059,f10064])).

fof(f11059,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f626,f391])).

fof(f626,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl9_28
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f9506,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X44,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0)
        | ~ l1_pre_topc(X44)
        | ~ v2_pre_topc(X44) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f9505,f97])).

fof(f97,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f9505,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X44,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X44)
        | ~ v2_pre_topc(X44) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f9380,f98])).

fof(f98,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f9380,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X44,sK1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X44)
        | ~ v2_pre_topc(X44) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(superposition,[],[f1092,f391])).

fof(f1092,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1091,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1091,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f487,f348])).

fof(f348,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl9_12
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f487,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f195,f109])).

fof(f195,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f11042,plain,
    ( ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | spl9_28
    | ~ spl9_36 ),
    inference(avatar_contradiction_clause,[],[f11041])).

fof(f11041,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | spl9_28
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f11040,f10564])).

fof(f10564,plain,
    ( ! [X3] : v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
    | ~ spl9_11 ),
    inference(global_subsumption,[],[f337,f8602])).

fof(f8602,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X3) ) ),
    inference(forward_demodulation,[],[f1304,f313])).

fof(f313,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f161,f109])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1304,plain,(
    ! [X3] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X3)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X3,k1_xboole_0) ) ),
    inference(resolution,[],[f245,f215])).

fof(f215,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f189,f185])).

fof(f185,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f189,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f245,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f156,f179])).

fof(f179,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f337,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl9_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f11040,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | spl9_28
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f11039,f10064])).

fof(f11039,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | spl9_28
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f11038,f337])).

fof(f11038,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27
    | spl9_28
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f11037,f10545])).

fof(f10545,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(global_subsumption,[],[f792])).

fof(f792,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f790])).

fof(f790,plain,
    ( spl9_36
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f11037,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | spl9_28 ),
    inference(forward_demodulation,[],[f627,f391])).

fof(f627,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_28 ),
    inference(avatar_component_clause,[],[f625])).

fof(f11021,plain,
    ( spl9_2
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_36 ),
    inference(avatar_contradiction_clause,[],[f11020])).

fof(f11020,plain,
    ( $false
    | spl9_2
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f11019,f10637])).

fof(f10637,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(global_subsumption,[],[f10633])).

fof(f11019,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl9_2
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f11018,f10155])).

fof(f10155,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f8832,f10064])).

fof(f8832,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f8802,f105])).

fof(f105,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f70])).

fof(f8802,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f205,f391])).

fof(f205,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl9_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f11018,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f10632,f10564])).

fof(f10632,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f10631,f10064])).

fof(f10631,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_11
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f10630,f337])).

fof(f10630,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f10629,f10545])).

fof(f10629,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10628,f391])).

fof(f10628,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f10627,f109])).

fof(f10627,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10626,f10064])).

fof(f10626,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10625,f184])).

fof(f10625,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10624,f391])).

fof(f10624,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10623,f10064])).

fof(f10623,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f10622,f391])).

fof(f10622,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f1444,f10064])).

fof(f1444,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1443,f267])).

fof(f267,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f265,f96])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f130,f95])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f1443,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1442,f592])).

fof(f592,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f255,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f255,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f110,f96])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1442,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1441,f97])).

fof(f1441,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1440,f98])).

fof(f1440,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f1439,f210])).

fof(f210,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f102,f105])).

fof(f102,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f1439,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f517,f209])).

fof(f209,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f103,f105])).

fof(f103,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

fof(f517,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f196,f208])).

fof(f208,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f104,f105])).

fof(f104,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f70])).

fof(f196,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f10608,plain,
    ( ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(avatar_contradiction_clause,[],[f10607])).

fof(f10607,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f10095,f10606])).

fof(f10606,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f10605,f95])).

fof(f10605,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f10604,f96])).

fof(f10604,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f10598,f10452])).

fof(f10598,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f10593,f10592])).

fof(f10592,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_17
    | ~ spl9_27
    | spl9_30 ),
    inference(superposition,[],[f634,f10064])).

fof(f634,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f633])).

fof(f10593,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(resolution,[],[f10172,f9504])).

fof(f9504,plain,
    ( ! [X42] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X42,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X42) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f9503,f97])).

fof(f9503,plain,
    ( ! [X42] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X42,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X42) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f9378,f98])).

fof(f9378,plain,
    ( ! [X42] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1)
        | ~ v5_pre_topc(k1_xboole_0,X42,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X42)
        | ~ v2_pre_topc(X42) )
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(superposition,[],[f1090,f391])).

fof(f1090,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1089,f109])).

fof(f1089,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f475,f348])).

fof(f475,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f194,f109])).

fof(f194,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f10172,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f9146,f10064])).

fof(f9146,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f626,f391])).

fof(f10095,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f200,f10064])).

fof(f200,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f199])).

fof(f10563,plain,
    ( ~ spl9_17
    | spl9_19
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f10562])).

fof(f10562,plain,
    ( $false
    | ~ spl9_17
    | spl9_19
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f10553,f10401])).

fof(f10401,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_17
    | spl9_19 ),
    inference(forward_demodulation,[],[f401,f391])).

fof(f401,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl9_19
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f10553,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_32 ),
    inference(resolution,[],[f756,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f756,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f754])).

fof(f754,plain,
    ( spl9_32
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f10543,plain,
    ( ~ spl9_17
    | spl9_19
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f10542])).

fof(f10542,plain,
    ( $false
    | ~ spl9_17
    | spl9_19
    | ~ spl9_35 ),
    inference(global_subsumption,[],[f10401,f788])).

fof(f788,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl9_35
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f10300,plain,
    ( ~ spl9_17
    | ~ spl9_27
    | spl9_48 ),
    inference(avatar_contradiction_clause,[],[f10299])).

fof(f10299,plain,
    ( $false
    | ~ spl9_17
    | ~ spl9_27
    | spl9_48 ),
    inference(subsumption_resolution,[],[f10298,f109])).

fof(f10298,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl9_17
    | ~ spl9_27
    | spl9_48 ),
    inference(forward_demodulation,[],[f10297,f10064])).

fof(f10297,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl9_17
    | spl9_48 ),
    inference(forward_demodulation,[],[f1565,f391])).

fof(f1565,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl9_48 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1563,plain,
    ( spl9_48
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f10022,plain,
    ( ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f10021])).

fof(f10021,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f10020,f95])).

fof(f10020,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f10019,f96])).

fof(f10019,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f10018,f8706])).

fof(f8706,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8603,f391])).

fof(f8603,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(superposition,[],[f100,f7160])).

fof(f7160,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f7159,f244])).

fof(f244,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f155,f109])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f7159,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7158,f184])).

fof(f7158,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2)
    | k1_xboole_0 = sK2
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7157,f402])).

fof(f402,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f400])).

fof(f7157,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7156,f184])).

fof(f7156,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4853,f402])).

fof(f4853,plain,
    ( sK2 = k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2)
    | ~ spl9_48 ),
    inference(resolution,[],[f4743,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f4743,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl9_48 ),
    inference(resolution,[],[f1564,f155])).

fof(f1564,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f10018,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_1
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f10017,f8807])).

fof(f8807,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f200,f7160])).

fof(f10017,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f10011,f9288])).

fof(f9288,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_19
    | spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f634,f7160])).

fof(f10011,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(resolution,[],[f9504,f9147])).

fof(f9147,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f9146,f7160])).

fof(f9264,plain,
    ( ~ spl9_19
    | spl9_39
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f9263])).

fof(f9263,plain,
    ( $false
    | ~ spl9_19
    | spl9_39
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f9262,f109])).

fof(f9262,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_19
    | spl9_39
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1079,f7160])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl9_39 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f1077,plain,
    ( spl9_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f9245,plain,
    ( spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f9244])).

fof(f9244,plain,
    ( $false
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_28
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f9243,f9147])).

fof(f9243,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f9242,f7160])).

fof(f9242,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f9241,f391])).

fof(f9241,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f9240,f109])).

fof(f9240,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f9239,f7160])).

fof(f9239,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f9238,f8834])).

fof(f8834,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_19
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f635,f7160])).

fof(f9238,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f8988,f8833])).

fof(f8833,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8832,f7160])).

fof(f8988,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8987,f184])).

fof(f8987,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8986,f391])).

fof(f8986,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8985,f7160])).

fof(f8985,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8984,f391])).

fof(f8984,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1444,f7160])).

fof(f9003,plain,
    ( ~ spl9_17
    | ~ spl9_19
    | spl9_28
    | ~ spl9_39
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f9002])).

fof(f9002,plain,
    ( $false
    | ~ spl9_17
    | ~ spl9_19
    | spl9_28
    | ~ spl9_39
    | ~ spl9_48 ),
    inference(global_subsumption,[],[f8847,f8858])).

fof(f8858,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_19
    | spl9_28
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8857,f7160])).

fof(f8857,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_17
    | spl9_28 ),
    inference(forward_demodulation,[],[f627,f391])).

fof(f8847,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_19
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7385,f7160])).

fof(f7385,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl9_19 ),
    inference(superposition,[],[f209,f402])).

fof(f8822,plain,
    ( ~ spl9_16
    | ~ spl9_19
    | ~ spl9_31
    | spl9_40
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f8821])).

fof(f8821,plain,
    ( $false
    | ~ spl9_16
    | ~ spl9_19
    | ~ spl9_31
    | spl9_40
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f8787,f8798])).

fof(f8798,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl9_19
    | spl9_40
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f1083,f7160])).

fof(f1083,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | spl9_40 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1081,plain,
    ( spl9_40
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f8787,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl9_16
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8786,f7160])).

fof(f8786,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl9_16
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8785,f402])).

fof(f8785,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_16
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f8784,f210])).

fof(f8784,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_16
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f4736,f873])).

fof(f873,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl9_16
    | ~ spl9_31 ),
    inference(superposition,[],[f387,f641])).

fof(f641,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl9_31
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f387,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl9_16
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f4736,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_48 ),
    inference(resolution,[],[f1564,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f8324,plain,
    ( ~ spl9_19
    | ~ spl9_31
    | ~ spl9_33
    | spl9_37
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f8323])).

fof(f8323,plain,
    ( $false
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_33
    | spl9_37
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f8322,f760])).

fof(f760,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f758])).

fof(f758,plain,
    ( spl9_33
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f8322,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl9_19
    | ~ spl9_31
    | spl9_37
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f8321,f7160])).

fof(f8321,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl9_31
    | spl9_37 ),
    inference(forward_demodulation,[],[f798,f641])).

fof(f798,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl9_37 ),
    inference(avatar_component_clause,[],[f797])).

fof(f797,plain,
    ( spl9_37
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f8259,plain,
    ( spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_37
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f8258])).

fof(f8258,plain,
    ( $false
    | spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_37
    | ~ spl9_48 ),
    inference(global_subsumption,[],[f1156,f3996,f7844])).

fof(f7844,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f7843,f334])).

fof(f334,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl9_10
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f7843,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7842,f337])).

fof(f7842,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7841,f7160])).

fof(f7841,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f7840,f334])).

fof(f7840,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7839,f337])).

fof(f7839,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f7838,f7160])).

fof(f7838,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f7837,f97])).

fof(f7837,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f7427,f98])).

fof(f7427,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_12
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(superposition,[],[f2523,f402])).

fof(f2523,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f2522,f95])).

fof(f2522,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f2517,f96])).

fof(f2517,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(superposition,[],[f1096,f641])).

fof(f1096,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1095,f109])).

fof(f1095,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f534,f348])).

fof(f534,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(k1_xboole_0,X0,X1)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f197,f109])).

fof(f197,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f3996,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_21
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f507,f1622])).

fof(f1622,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(resolution,[],[f1573,f129])).

fof(f1573,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(global_subsumption,[],[f1127])).

fof(f1127,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(global_subsumption,[],[f818,f1110])).

fof(f1110,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(sK2)
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f269,f641])).

fof(f269,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f141,f101])).

fof(f101,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f818,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f799,f641])).

fof(f799,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f797])).

fof(f507,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl9_21
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f1156,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_1
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(superposition,[],[f201,f1140])).

fof(f1140,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(resolution,[],[f1127,f129])).

fof(f6319,plain,
    ( spl9_22
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f6318])).

fof(f6318,plain,
    ( $false
    | spl9_22
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(global_subsumption,[],[f553,f6317])).

fof(f6317,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl9_30
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f635,f641])).

fof(f553,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl9_22
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f6267,plain,
    ( ~ spl9_1
    | spl9_19
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f6266])).

fof(f6266,plain,
    ( $false
    | ~ spl9_1
    | spl9_19
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6265,f863])).

fof(f863,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_31 ),
    inference(superposition,[],[f100,f641])).

fof(f6265,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl9_1
    | spl9_19
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f6264,f4630])).

fof(f4630,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl9_19
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f4103,f1965])).

fof(f1965,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_31 ),
    inference(superposition,[],[f312,f641])).

fof(f312,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(resolution,[],[f161,f208])).

fof(f4103,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | spl9_19
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f3444,f401])).

fof(f3444,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f3380,f866])).

fof(f866,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_31 ),
    inference(superposition,[],[f209,f641])).

fof(f3380,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_31 ),
    inference(resolution,[],[f865,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f94])).

fof(f865,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl9_31 ),
    inference(superposition,[],[f208,f641])).

fof(f6264,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6263,f97])).

fof(f6263,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6262,f98])).

fof(f6262,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6261,f863])).

fof(f6261,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6260,f864])).

fof(f864,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl9_31 ),
    inference(superposition,[],[f101,f641])).

fof(f6260,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6259,f210])).

fof(f6259,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | spl9_30
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6258,f3911])).

fof(f3911,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | spl9_30
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f634,f641])).

fof(f6258,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f6191,f200])).

fof(f6191,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(resolution,[],[f937,f1462])).

fof(f1462,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f630,f641])).

fof(f630,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl9_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f937,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))))
        | ~ v5_pre_topc(X3,sK0,X4)
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4)
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) )
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f936,f95])).

fof(f936,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))))
        | ~ v5_pre_topc(X3,sK0,X4)
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4)
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f891,f96])).

fof(f891,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))))
        | ~ v5_pre_topc(X3,sK0,X4)
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4)
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_31 ),
    inference(superposition,[],[f194,f641])).

fof(f4502,plain,
    ( ~ spl9_31
    | spl9_37
    | spl9_38
    | ~ spl9_39 ),
    inference(avatar_contradiction_clause,[],[f4501])).

fof(f4501,plain,
    ( $false
    | ~ spl9_31
    | spl9_37
    | spl9_38
    | ~ spl9_39 ),
    inference(global_subsumption,[],[f1942,f1107,f4500])).

fof(f4500,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl9_31
    | spl9_37 ),
    inference(forward_demodulation,[],[f798,f641])).

fof(f1107,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(sK2)
    | ~ spl9_31
    | spl9_38 ),
    inference(forward_demodulation,[],[f1106,f641])).

fof(f1106,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | spl9_38 ),
    inference(subsumption_resolution,[],[f763,f802])).

fof(f802,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl9_38 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl9_38
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f763,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f762,f210])).

fof(f762,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f372,f100])).

fof(f372,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f146,f101])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f1942,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_39 ),
    inference(resolution,[],[f283,f1078])).

fof(f1078,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f283,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f273,f108])).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f273,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X3)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f141,f185])).

fof(f3995,plain,
    ( ~ spl9_10
    | ~ spl9_11
    | ~ spl9_31
    | ~ spl9_37
    | spl9_49 ),
    inference(avatar_contradiction_clause,[],[f3994])).

fof(f3994,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_31
    | ~ spl9_37
    | spl9_49 ),
    inference(subsumption_resolution,[],[f3993,f334])).

fof(f3993,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_11
    | ~ spl9_31
    | ~ spl9_37
    | spl9_49 ),
    inference(forward_demodulation,[],[f3992,f337])).

fof(f3992,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_31
    | ~ spl9_37
    | spl9_49 ),
    inference(forward_demodulation,[],[f1569,f1622])).

fof(f1569,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl9_49 ),
    inference(avatar_component_clause,[],[f1567])).

fof(f1567,plain,
    ( spl9_49
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f3908,plain,
    ( ~ spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_21
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(avatar_contradiction_clause,[],[f3907])).

fof(f3907,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | spl9_21
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(global_subsumption,[],[f3551,f3423])).

fof(f3423,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f3422,f97])).

fof(f3422,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f3417,f98])).

fof(f3417,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_1
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(resolution,[],[f2500,f1762])).

fof(f1762,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(superposition,[],[f200,f1622])).

fof(f2500,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f2499,f334])).

fof(f2499,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f2498,f337])).

fof(f2498,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f2497,f1622])).

fof(f2497,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f2496,f334])).

fof(f2496,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f2495,f337])).

fof(f2495,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f2494,f1622])).

fof(f2494,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f2493,f95])).

fof(f2493,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f2488,f96])).

fof(f2488,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_12
    | ~ spl9_31 ),
    inference(superposition,[],[f1094,f641])).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1093,f109])).

fof(f1093,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
        | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f518,f348])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X0,X1)
      | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f196,f109])).

fof(f3551,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_21
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f506,f1622])).

fof(f506,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_21 ),
    inference(avatar_component_clause,[],[f505])).

fof(f1588,plain,
    ( ~ spl9_19
    | ~ spl9_31
    | spl9_48 ),
    inference(avatar_contradiction_clause,[],[f1587])).

fof(f1587,plain,
    ( $false
    | ~ spl9_19
    | ~ spl9_31
    | spl9_48 ),
    inference(global_subsumption,[],[f903,f1583])).

fof(f1583,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_19
    | ~ spl9_31
    | spl9_48 ),
    inference(forward_demodulation,[],[f1582,f184])).

fof(f1582,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl9_19
    | ~ spl9_31
    | spl9_48 ),
    inference(forward_demodulation,[],[f1565,f1574])).

fof(f1574,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(global_subsumption,[],[f402])).

fof(f903,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f902,f184])).

fof(f902,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f865,f402])).

fof(f1570,plain,
    ( ~ spl9_48
    | ~ spl9_49
    | spl9_2
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f1561,f639,f505,f203,f1567,f1563])).

fof(f1561,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl9_2
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1473,f1465])).

fof(f1465,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1464,f105])).

fof(f1464,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl9_2
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f205,f641])).

fof(f1473,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1472,f641])).

fof(f1472,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1461,f641])).

fof(f1461,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_21
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1460,f641])).

fof(f1460,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1459,f95])).

fof(f1459,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1458,f96])).

fof(f1458,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1457,f268])).

fof(f268,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f266,f98])).

fof(f266,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f130,f97])).

fof(f1457,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1456,f1046])).

fof(f1046,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f256,f144])).

fof(f256,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f110,f98])).

fof(f1456,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1455,f210])).

fof(f1455,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1454,f209])).

fof(f1454,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f474,f507])).

fof(f474,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f194,f208])).

fof(f1557,plain,
    ( spl9_2
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1556])).

fof(f1556,plain,
    ( $false
    | spl9_2
    | ~ spl9_22
    | ~ spl9_28
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(global_subsumption,[],[f1298,f1476,f1462,f1465])).

fof(f1476,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_22
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1448,f641])).

fof(f1448,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_22
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1447,f641])).

fof(f1447,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_22
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1446,f641])).

fof(f1446,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_22
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1445,f554])).

fof(f554,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f552])).

fof(f1445,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1444,f641])).

fof(f1298,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_28
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f626,f641])).

fof(f1430,plain,
    ( spl9_19
    | spl9_29
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1429])).

fof(f1429,plain,
    ( $false
    | spl9_19
    | spl9_29
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1428,f864])).

fof(f1428,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | spl9_19
    | spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1427,f1189])).

fof(f1189,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl9_19
    | ~ spl9_31 ),
    inference(global_subsumption,[],[f401,f1188])).

fof(f1188,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1187,f641])).

fof(f1187,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f416,f312])).

fof(f416,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(subsumption_resolution,[],[f409,f209])).

fof(f409,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    inference(resolution,[],[f162,f208])).

fof(f1427,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f631,f641])).

fof(f631,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl9_29 ),
    inference(avatar_component_clause,[],[f629])).

fof(f1394,plain,
    ( spl9_1
    | spl9_19
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1393])).

fof(f1393,plain,
    ( $false
    | spl9_1
    | spl9_19
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1392,f863])).

fof(f1392,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | spl9_1
    | spl9_19
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1391,f1189])).

fof(f1391,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1390,f641])).

fof(f1390,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1389,f554])).

fof(f1389,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_29
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1388,f641])).

fof(f1388,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1387,f95])).

fof(f1387,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1386,f96])).

fof(f1386,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1385,f97])).

fof(f1385,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1384,f98])).

fof(f1384,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1383,f100])).

fof(f1383,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1382,f101])).

fof(f1382,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1381,f210])).

fof(f1381,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl9_1
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1364,f201])).

fof(f1364,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_29 ),
    inference(resolution,[],[f630,f195])).

fof(f1297,plain,
    ( spl9_19
    | spl9_28
    | ~ spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | spl9_19
    | spl9_28
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1295,f863])).

fof(f1295,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | spl9_19
    | spl9_28
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1294,f1189])).

fof(f1294,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl9_28
    | ~ spl9_31 ),
    inference(superposition,[],[f627,f641])).

fof(f1196,plain,
    ( spl9_11
    | ~ spl9_33 ),
    inference(avatar_contradiction_clause,[],[f1195])).

fof(f1195,plain,
    ( $false
    | spl9_11
    | ~ spl9_33 ),
    inference(subsumption_resolution,[],[f1194,f338])).

fof(f338,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f336])).

fof(f1194,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_33 ),
    inference(resolution,[],[f760,f129])).

fof(f1137,plain,
    ( ~ spl9_19
    | ~ spl9_31
    | spl9_39 ),
    inference(avatar_contradiction_clause,[],[f1136])).

fof(f1136,plain,
    ( $false
    | ~ spl9_19
    | ~ spl9_31
    | spl9_39 ),
    inference(subsumption_resolution,[],[f1079,f903])).

fof(f1135,plain,
    ( spl9_21
    | ~ spl9_40
    | ~ spl9_2
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f1134,f639,f400,f203,f1081,f505])).

fof(f1134,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1133,f641])).

fof(f1133,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(forward_demodulation,[],[f1132,f402])).

fof(f1132,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_2
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1131,f903])).

fof(f1131,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_2
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f1130,f184])).

fof(f1130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_2
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f1129,f402])).

fof(f1129,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f495,f1046])).

fof(f495,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f494,f95])).

fof(f494,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f493,f96])).

fof(f493,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f492,f268])).

fof(f492,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f491,f210])).

fof(f491,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f490,f209])).

fof(f490,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f486,f218])).

fof(f218,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f204,f105])).

fof(f204,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f203])).

fof(f486,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f195,f208])).

fof(f1109,plain,
    ( spl9_4
    | ~ spl9_19
    | ~ spl9_31
    | spl9_38 ),
    inference(avatar_contradiction_clause,[],[f1108])).

fof(f1108,plain,
    ( $false
    | spl9_4
    | ~ spl9_19
    | ~ spl9_31
    | spl9_38 ),
    inference(global_subsumption,[],[f233,f1101])).

fof(f1101,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f1100,f108])).

fof(f1100,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f285,f402])).

fof(f285,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f142,f208])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f233,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl9_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1099,plain,
    ( spl9_4
    | spl9_17
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(avatar_contradiction_clause,[],[f1098])).

fof(f1098,plain,
    ( $false
    | spl9_4
    | spl9_17
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(global_subsumption,[],[f448,f818])).

fof(f448,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl9_4
    | spl9_17 ),
    inference(superposition,[],[f274,f415])).

fof(f415,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | spl9_17 ),
    inference(forward_demodulation,[],[f414,f311])).

fof(f311,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f161,f101])).

fof(f414,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f413,f390])).

fof(f390,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f389])).

fof(f413,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f408,f100])).

fof(f408,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f162,f101])).

fof(f274,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl9_4 ),
    inference(subsumption_resolution,[],[f269,f233])).

fof(f845,plain,
    ( ~ spl9_4
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f844])).

fof(f844,plain,
    ( $false
    | ~ spl9_4
    | spl9_12 ),
    inference(subsumption_resolution,[],[f832,f349])).

fof(f349,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f347])).

fof(f832,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl9_4 ),
    inference(superposition,[],[f210,f812])).

fof(f812,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_4 ),
    inference(resolution,[],[f234,f129])).

fof(f234,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f232])).

fof(f821,plain,
    ( ~ spl9_4
    | ~ spl9_31
    | spl9_33
    | ~ spl9_37 ),
    inference(avatar_contradiction_clause,[],[f820])).

fof(f820,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_31
    | spl9_33
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f819,f759])).

fof(f759,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl9_33 ),
    inference(avatar_component_clause,[],[f758])).

fof(f819,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl9_4
    | ~ spl9_31
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f818,f812])).

fof(f817,plain,
    ( spl9_17
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f816])).

fof(f816,plain,
    ( $false
    | spl9_17
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f815,f390])).

fof(f815,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_38 ),
    inference(resolution,[],[f803,f129])).

fof(f803,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f801])).

fof(f793,plain,
    ( spl9_35
    | spl9_36
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f784,f617,f389,f790,f786])).

fof(f784,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f783,f654])).

fof(f654,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f653,f184])).

fof(f653,plain,
    ( sK2 = k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f619,f391])).

fof(f783,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f782,f312])).

fof(f782,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f416,f391])).

fof(f761,plain,
    ( spl9_32
    | spl9_33
    | ~ spl9_17
    | spl9_19
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f752,f617,f400,f389,f758,f754])).

fof(f752,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_17
    | spl9_19
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f751,f654])).

fof(f751,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl9_17
    | spl9_19
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f750,f418])).

fof(f418,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | spl9_19 ),
    inference(forward_demodulation,[],[f417,f312])).

fof(f417,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | spl9_19 ),
    inference(subsumption_resolution,[],[f416,f401])).

fof(f750,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f749,f391])).

fof(f749,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f748,f108])).

fof(f748,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_17
    | ~ spl9_27 ),
    inference(forward_demodulation,[],[f747,f654])).

fof(f747,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f746,f210])).

fof(f746,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(subsumption_resolution,[],[f373,f209])).

fof(f373,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f146,f208])).

fof(f707,plain,
    ( spl9_4
    | ~ spl9_17 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | spl9_4
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f668,f108])).

fof(f668,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_4
    | ~ spl9_17 ),
    inference(superposition,[],[f532,f391])).

fof(f532,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl9_4 ),
    inference(subsumption_resolution,[],[f284,f233])).

fof(f284,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f142,f101])).

fof(f697,plain,
    ( ~ spl9_17
    | spl9_29 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | ~ spl9_17
    | spl9_29 ),
    inference(subsumption_resolution,[],[f695,f644])).

fof(f644,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_17
    | spl9_29 ),
    inference(forward_demodulation,[],[f643,f184])).

fof(f643,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl9_17
    | spl9_29 ),
    inference(forward_demodulation,[],[f631,f391])).

fof(f695,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f659,f184])).

fof(f659,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl9_17 ),
    inference(superposition,[],[f101,f391])).

fof(f652,plain,
    ( ~ spl9_17
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl9_17
    | spl9_26 ),
    inference(subsumption_resolution,[],[f650,f244])).

fof(f650,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl9_17
    | spl9_26 ),
    inference(forward_demodulation,[],[f649,f184])).

fof(f649,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK2)
    | ~ spl9_17
    | spl9_26 ),
    inference(forward_demodulation,[],[f615,f391])).

fof(f615,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl9_26
  <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f642,plain,
    ( spl9_17
    | spl9_31 ),
    inference(avatar_split_clause,[],[f637,f639,f389])).

fof(f637,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f413,f311])).

fof(f636,plain,
    ( ~ spl9_28
    | ~ spl9_29
    | spl9_30
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f623,f203,f633,f629,f625])).

fof(f623,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f542,f592])).

fof(f542,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f541,f267])).

fof(f541,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f540,f97])).

fof(f540,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f539,f98])).

fof(f539,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f538,f210])).

fof(f538,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f537,f209])).

fof(f537,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f533,f218])).

fof(f533,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f197,f208])).

fof(f620,plain,
    ( ~ spl9_26
    | spl9_27 ),
    inference(avatar_split_clause,[],[f577,f617,f613])).

fof(f577,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2
    | ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2) ),
    inference(resolution,[],[f242,f150])).

fof(f242,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f155,f101])).

fof(f392,plain,
    ( spl9_16
    | spl9_17 ),
    inference(avatar_split_clause,[],[f383,f389,f385])).

fof(f383,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f382,f210])).

fof(f382,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f377,f100])).

fof(f377,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f192,f101])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f339,plain,
    ( spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f331,f336,f333])).

fof(f331,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f330,f313])).

fof(f330,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f215,f109])).

fof(f207,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f106,f203,f199])).

fof(f106,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f206,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f107,f203,f199])).

fof(f107,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (16026)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (16033)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (16028)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (16039)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (16046)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (16025)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (16049)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (16031)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (16048)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (16041)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (16038)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (16045)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (16029)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (16035)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (16043)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (16042)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (16034)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (16037)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (16032)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (16047)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (16030)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (16030)Refutation not found, incomplete strategy% (16030)------------------------------
% 0.21/0.53  % (16030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16030)Memory used [KB]: 10746
% 0.21/0.53  % (16030)Time elapsed: 0.114 s
% 0.21/0.53  % (16030)------------------------------
% 0.21/0.53  % (16030)------------------------------
% 0.21/0.53  % (16040)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (16024)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (16036)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (16024)Refutation not found, incomplete strategy% (16024)------------------------------
% 0.21/0.53  % (16024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16024)Memory used [KB]: 10618
% 0.21/0.53  % (16024)Time elapsed: 0.126 s
% 0.21/0.53  % (16024)------------------------------
% 0.21/0.53  % (16024)------------------------------
% 0.21/0.53  % (16037)Refutation not found, incomplete strategy% (16037)------------------------------
% 0.21/0.53  % (16037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16037)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16037)Memory used [KB]: 6268
% 0.21/0.53  % (16037)Time elapsed: 0.128 s
% 0.21/0.53  % (16037)------------------------------
% 0.21/0.53  % (16037)------------------------------
% 0.21/0.54  % (16027)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (16029)Refutation not found, incomplete strategy% (16029)------------------------------
% 0.21/0.54  % (16029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16029)Memory used [KB]: 6268
% 0.21/0.54  % (16029)Time elapsed: 0.139 s
% 0.21/0.54  % (16029)------------------------------
% 0.21/0.54  % (16029)------------------------------
% 0.21/0.55  % (16044)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 2.08/0.63  % (16033)Refutation not found, incomplete strategy% (16033)------------------------------
% 2.08/0.63  % (16033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.63  % (16033)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.63  
% 2.08/0.63  % (16033)Memory used [KB]: 6268
% 2.08/0.63  % (16033)Time elapsed: 0.208 s
% 2.08/0.63  % (16033)------------------------------
% 2.08/0.63  % (16033)------------------------------
% 4.19/0.91  % (16038)Time limit reached!
% 4.19/0.91  % (16038)------------------------------
% 4.19/0.91  % (16038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.19/0.91  % (16038)Termination reason: Time limit
% 4.19/0.91  
% 4.19/0.91  % (16038)Memory used [KB]: 8315
% 4.19/0.91  % (16038)Time elapsed: 0.505 s
% 4.19/0.91  % (16038)------------------------------
% 4.19/0.91  % (16038)------------------------------
% 7.22/1.31  % (16032)Time limit reached!
% 7.22/1.31  % (16032)------------------------------
% 7.22/1.31  % (16032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.22/1.31  % (16032)Termination reason: Time limit
% 7.22/1.31  % (16032)Termination phase: Saturation
% 7.22/1.31  
% 7.22/1.31  % (16032)Memory used [KB]: 5628
% 7.22/1.31  % (16032)Time elapsed: 0.900 s
% 7.22/1.31  % (16032)------------------------------
% 7.22/1.31  % (16032)------------------------------
% 8.49/1.43  % (16025)Time limit reached!
% 8.49/1.43  % (16025)------------------------------
% 8.49/1.43  % (16025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.49/1.43  % (16025)Termination reason: Time limit
% 8.49/1.43  
% 8.49/1.43  % (16025)Memory used [KB]: 17526
% 8.49/1.43  % (16025)Time elapsed: 1.021 s
% 8.49/1.43  % (16025)------------------------------
% 8.49/1.43  % (16025)------------------------------
% 9.26/1.54  % (16028)Time limit reached!
% 9.26/1.54  % (16028)------------------------------
% 9.26/1.54  % (16028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.26/1.54  % (16028)Termination reason: Time limit
% 9.26/1.54  % (16028)Termination phase: Saturation
% 9.26/1.54  
% 9.26/1.54  % (16028)Memory used [KB]: 13944
% 9.26/1.54  % (16028)Time elapsed: 1.100 s
% 9.26/1.54  % (16028)------------------------------
% 9.26/1.54  % (16028)------------------------------
% 12.04/1.91  % (16034)Refutation found. Thanks to Tanya!
% 12.04/1.91  % SZS status Theorem for theBenchmark
% 12.04/1.91  % SZS output start Proof for theBenchmark
% 12.04/1.91  fof(f11314,plain,(
% 12.04/1.91    $false),
% 12.04/1.91    inference(avatar_sat_refutation,[],[f206,f207,f339,f392,f620,f636,f642,f652,f697,f707,f761,f793,f817,f821,f845,f1099,f1109,f1135,f1137,f1196,f1297,f1394,f1430,f1557,f1570,f1588,f3908,f3995,f4502,f6267,f6319,f8259,f8324,f8822,f9003,f9245,f9264,f10022,f10300,f10543,f10563,f10608,f11021,f11042,f11313])).
% 12.04/1.91  fof(f11313,plain,(
% 12.04/1.91    spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30),
% 12.04/1.91    inference(avatar_contradiction_clause,[],[f11312])).
% 12.04/1.91  fof(f11312,plain,(
% 12.04/1.91    $false | (spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11311,f95])).
% 12.04/1.91  fof(f95,plain,(
% 12.04/1.91    v2_pre_topc(sK0)),
% 12.04/1.91    inference(cnf_transformation,[],[f70])).
% 12.04/1.91  fof(f70,plain,(
% 12.04/1.91    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 12.04/1.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68,f67,f66])).
% 12.04/1.91  fof(f66,plain,(
% 12.04/1.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 12.04/1.91    introduced(choice_axiom,[])).
% 12.04/1.91  fof(f67,plain,(
% 12.04/1.91    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 12.04/1.91    introduced(choice_axiom,[])).
% 12.04/1.91  fof(f68,plain,(
% 12.04/1.91    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 12.04/1.91    introduced(choice_axiom,[])).
% 12.04/1.91  fof(f69,plain,(
% 12.04/1.91    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 12.04/1.91    introduced(choice_axiom,[])).
% 12.04/1.91  fof(f65,plain,(
% 12.04/1.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.04/1.91    inference(flattening,[],[f64])).
% 12.04/1.91  fof(f64,plain,(
% 12.04/1.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.04/1.91    inference(nnf_transformation,[],[f34])).
% 12.04/1.91  fof(f34,plain,(
% 12.04/1.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.04/1.91    inference(flattening,[],[f33])).
% 12.04/1.91  fof(f33,plain,(
% 12.04/1.91    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 12.04/1.91    inference(ennf_transformation,[],[f29])).
% 12.04/1.91  fof(f29,negated_conjecture,(
% 12.04/1.91    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.04/1.91    inference(negated_conjecture,[],[f28])).
% 12.04/1.91  fof(f28,conjecture,(
% 12.04/1.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 12.04/1.91  fof(f11311,plain,(
% 12.04/1.91    ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11310,f96])).
% 12.04/1.91  fof(f96,plain,(
% 12.04/1.91    l1_pre_topc(sK0)),
% 12.04/1.91    inference(cnf_transformation,[],[f70])).
% 12.04/1.91  fof(f11310,plain,(
% 12.04/1.91    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11309,f10452])).
% 12.04/1.91  fof(f10452,plain,(
% 12.04/1.91    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl9_17 | ~spl9_27)),
% 12.04/1.91    inference(forward_demodulation,[],[f10408,f391])).
% 12.04/1.91  fof(f391,plain,(
% 12.04/1.91    k1_xboole_0 = u1_struct_0(sK1) | ~spl9_17),
% 12.04/1.91    inference(avatar_component_clause,[],[f389])).
% 12.04/1.91  fof(f389,plain,(
% 12.04/1.91    spl9_17 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 12.04/1.91  fof(f10408,plain,(
% 12.04/1.91    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.91    inference(superposition,[],[f100,f10064])).
% 12.04/1.91  fof(f10064,plain,(
% 12.04/1.91    k1_xboole_0 = sK2 | (~spl9_17 | ~spl9_27)),
% 12.04/1.91    inference(forward_demodulation,[],[f10063,f184])).
% 12.04/1.91  fof(f184,plain,(
% 12.04/1.91    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 12.04/1.91    inference(equality_resolution,[],[f159])).
% 12.04/1.91  fof(f159,plain,(
% 12.04/1.91    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 12.04/1.91    inference(cnf_transformation,[],[f93])).
% 12.04/1.91  fof(f93,plain,(
% 12.04/1.91    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.04/1.91    inference(flattening,[],[f92])).
% 12.04/1.91  fof(f92,plain,(
% 12.04/1.91    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.04/1.91    inference(nnf_transformation,[],[f7])).
% 12.04/1.91  fof(f7,axiom,(
% 12.04/1.91    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 12.04/1.91  fof(f10063,plain,(
% 12.04/1.91    sK2 = k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0) | (~spl9_17 | ~spl9_27)),
% 12.04/1.91    inference(forward_demodulation,[],[f619,f391])).
% 12.04/1.91  fof(f619,plain,(
% 12.04/1.91    k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2 | ~spl9_27),
% 12.04/1.91    inference(avatar_component_clause,[],[f617])).
% 12.04/1.91  fof(f617,plain,(
% 12.04/1.91    spl9_27 <=> k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 12.04/1.91  fof(f100,plain,(
% 12.04/1.91    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 12.04/1.91    inference(cnf_transformation,[],[f70])).
% 12.04/1.91  fof(f11309,plain,(
% 12.04/1.91    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11308,f10633])).
% 12.04/1.91  fof(f10633,plain,(
% 12.04/1.91    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_17 | ~spl9_27 | ~spl9_30)),
% 12.04/1.91    inference(forward_demodulation,[],[f635,f10064])).
% 12.04/1.91  fof(f635,plain,(
% 12.04/1.91    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl9_30),
% 12.04/1.91    inference(avatar_component_clause,[],[f633])).
% 12.04/1.91  fof(f633,plain,(
% 12.04/1.91    spl9_30 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 12.04/1.91  fof(f11308,plain,(
% 12.04/1.91    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11305,f11068])).
% 12.04/1.91  fof(f11068,plain,(
% 12.04/1.91    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl9_1 | ~spl9_17 | ~spl9_27)),
% 12.04/1.91    inference(forward_demodulation,[],[f201,f10064])).
% 12.04/1.91  fof(f201,plain,(
% 12.04/1.91    ~v5_pre_topc(sK2,sK0,sK1) | spl9_1),
% 12.04/1.91    inference(avatar_component_clause,[],[f199])).
% 12.04/1.91  fof(f199,plain,(
% 12.04/1.91    spl9_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 12.04/1.91  fof(f11305,plain,(
% 12.04/1.91    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28)),
% 12.04/1.91    inference(resolution,[],[f9506,f11266])).
% 12.04/1.91  fof(f11266,plain,(
% 12.04/1.91    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_27 | ~spl9_28)),
% 12.04/1.91    inference(forward_demodulation,[],[f11059,f10064])).
% 12.04/1.91  fof(f11059,plain,(
% 12.04/1.91    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_28)),
% 12.04/1.91    inference(forward_demodulation,[],[f626,f391])).
% 12.04/1.91  fof(f626,plain,(
% 12.04/1.91    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl9_28),
% 12.04/1.91    inference(avatar_component_clause,[],[f625])).
% 12.04/1.91  fof(f625,plain,(
% 12.04/1.91    spl9_28 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 12.04/1.91  fof(f9506,plain,(
% 12.04/1.91    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X44,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.91    inference(subsumption_resolution,[],[f9505,f97])).
% 12.04/1.91  fof(f97,plain,(
% 12.04/1.91    v2_pre_topc(sK1)),
% 12.04/1.91    inference(cnf_transformation,[],[f70])).
% 12.04/1.91  fof(f9505,plain,(
% 12.04/1.91    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X44,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.91    inference(subsumption_resolution,[],[f9380,f98])).
% 12.04/1.91  fof(f98,plain,(
% 12.04/1.91    l1_pre_topc(sK1)),
% 12.04/1.91    inference(cnf_transformation,[],[f70])).
% 12.04/1.91  fof(f9380,plain,(
% 12.04/1.91    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X44,sK1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X44),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.91    inference(superposition,[],[f1092,f391])).
% 12.04/1.91  fof(f1092,plain,(
% 12.04/1.91    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.04/1.91    inference(subsumption_resolution,[],[f1091,f109])).
% 12.04/1.91  fof(f109,plain,(
% 12.04/1.91    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 12.04/1.91    inference(cnf_transformation,[],[f10])).
% 12.04/1.91  fof(f10,axiom,(
% 12.04/1.91    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 12.04/1.91  fof(f1091,plain,(
% 12.04/1.91    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.04/1.91    inference(subsumption_resolution,[],[f487,f348])).
% 12.04/1.91  fof(f348,plain,(
% 12.04/1.91    v1_funct_1(k1_xboole_0) | ~spl9_12),
% 12.04/1.91    inference(avatar_component_clause,[],[f347])).
% 12.04/1.91  fof(f347,plain,(
% 12.04/1.91    spl9_12 <=> v1_funct_1(k1_xboole_0)),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 12.04/1.91  fof(f487,plain,(
% 12.04/1.91    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.91    inference(resolution,[],[f195,f109])).
% 12.04/1.91  fof(f195,plain,(
% 12.04/1.91    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.91    inference(duplicate_literal_removal,[],[f177])).
% 12.04/1.91  fof(f177,plain,(
% 12.04/1.91    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.91    inference(equality_resolution,[],[f134])).
% 12.04/1.91  fof(f134,plain,(
% 12.04/1.91    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.91    inference(cnf_transformation,[],[f79])).
% 12.04/1.91  fof(f79,plain,(
% 12.04/1.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.04/1.91    inference(nnf_transformation,[],[f44])).
% 12.04/1.91  fof(f44,plain,(
% 12.04/1.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.04/1.91    inference(flattening,[],[f43])).
% 12.04/1.91  fof(f43,plain,(
% 12.04/1.91    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.04/1.91    inference(ennf_transformation,[],[f26])).
% 12.04/1.91  fof(f26,axiom,(
% 12.04/1.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 12.04/1.91  fof(f11042,plain,(
% 12.04/1.91    ~spl9_11 | ~spl9_17 | ~spl9_27 | spl9_28 | ~spl9_36),
% 12.04/1.91    inference(avatar_contradiction_clause,[],[f11041])).
% 12.04/1.91  fof(f11041,plain,(
% 12.04/1.91    $false | (~spl9_11 | ~spl9_17 | ~spl9_27 | spl9_28 | ~spl9_36)),
% 12.04/1.91    inference(subsumption_resolution,[],[f11040,f10564])).
% 12.04/1.91  fof(f10564,plain,(
% 12.04/1.91    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3)) ) | ~spl9_11),
% 12.04/1.91    inference(global_subsumption,[],[f337,f8602])).
% 12.04/1.91  fof(f8602,plain,(
% 12.04/1.91    ( ! [X3] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X3)) )),
% 12.04/1.91    inference(forward_demodulation,[],[f1304,f313])).
% 12.04/1.91  fof(f313,plain,(
% 12.04/1.91    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 12.04/1.91    inference(resolution,[],[f161,f109])).
% 12.04/1.91  fof(f161,plain,(
% 12.04/1.91    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 12.04/1.91    inference(cnf_transformation,[],[f53])).
% 12.04/1.91  fof(f53,plain,(
% 12.04/1.91    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.04/1.91    inference(ennf_transformation,[],[f16])).
% 12.04/1.91  fof(f16,axiom,(
% 12.04/1.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 12.04/1.91  fof(f1304,plain,(
% 12.04/1.91    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X3,k1_xboole_0)) )),
% 12.04/1.91    inference(resolution,[],[f245,f215])).
% 12.04/1.91  fof(f215,plain,(
% 12.04/1.91    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 12.04/1.91    inference(forward_demodulation,[],[f189,f185])).
% 12.04/1.91  fof(f185,plain,(
% 12.04/1.91    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 12.04/1.91    inference(equality_resolution,[],[f158])).
% 12.04/1.91  fof(f158,plain,(
% 12.04/1.91    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 12.04/1.91    inference(cnf_transformation,[],[f93])).
% 12.04/1.91  fof(f189,plain,(
% 12.04/1.91    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 12.04/1.91    inference(equality_resolution,[],[f165])).
% 12.04/1.91  fof(f165,plain,(
% 12.04/1.91    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.04/1.91    inference(cnf_transformation,[],[f94])).
% 12.04/1.91  fof(f94,plain,(
% 12.04/1.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.04/1.91    inference(nnf_transformation,[],[f55])).
% 12.04/1.91  fof(f55,plain,(
% 12.04/1.91    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.04/1.91    inference(flattening,[],[f54])).
% 12.04/1.91  fof(f54,plain,(
% 12.04/1.91    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.04/1.91    inference(ennf_transformation,[],[f20])).
% 12.04/1.91  fof(f20,axiom,(
% 12.04/1.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 12.04/1.91  fof(f245,plain,(
% 12.04/1.91    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 12.04/1.91    inference(resolution,[],[f156,f179])).
% 12.04/1.91  fof(f179,plain,(
% 12.04/1.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.04/1.91    inference(equality_resolution,[],[f149])).
% 12.04/1.91  fof(f149,plain,(
% 12.04/1.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 12.04/1.91    inference(cnf_transformation,[],[f86])).
% 12.04/1.91  fof(f86,plain,(
% 12.04/1.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.04/1.91    inference(flattening,[],[f85])).
% 12.04/1.91  fof(f85,plain,(
% 12.04/1.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.04/1.91    inference(nnf_transformation,[],[f4])).
% 12.04/1.91  fof(f4,axiom,(
% 12.04/1.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.04/1.91  fof(f156,plain,(
% 12.04/1.91    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.04/1.91    inference(cnf_transformation,[],[f91])).
% 12.04/1.91  fof(f91,plain,(
% 12.04/1.91    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.04/1.91    inference(nnf_transformation,[],[f11])).
% 12.04/1.91  fof(f11,axiom,(
% 12.04/1.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.04/1.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 12.04/1.91  fof(f337,plain,(
% 12.04/1.91    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_11),
% 12.04/1.91    inference(avatar_component_clause,[],[f336])).
% 12.04/1.91  fof(f336,plain,(
% 12.04/1.91    spl9_11 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 12.04/1.91    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 12.04/1.91  fof(f11040,plain,(
% 12.04/1.91    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl9_11 | ~spl9_17 | ~spl9_27 | spl9_28 | ~spl9_36)),
% 12.04/1.91    inference(forward_demodulation,[],[f11039,f10064])).
% 12.04/1.91  fof(f11039,plain,(
% 12.04/1.91    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl9_11 | ~spl9_17 | ~spl9_27 | spl9_28 | ~spl9_36)),
% 12.04/1.91    inference(forward_demodulation,[],[f11038,f337])).
% 12.04/1.91  fof(f11038,plain,(
% 12.04/1.91    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl9_17 | ~spl9_27 | spl9_28 | ~spl9_36)),
% 12.04/1.91    inference(forward_demodulation,[],[f11037,f10545])).
% 12.04/1.91  fof(f10545,plain,(
% 12.04/1.91    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.91    inference(global_subsumption,[],[f792])).
% 12.04/1.93  fof(f792,plain,(
% 12.04/1.93    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl9_36),
% 12.04/1.93    inference(avatar_component_clause,[],[f790])).
% 12.04/1.93  fof(f790,plain,(
% 12.04/1.93    spl9_36 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)),
% 12.04/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 12.04/1.93  fof(f11037,plain,(
% 12.04/1.93    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | spl9_28)),
% 12.04/1.93    inference(forward_demodulation,[],[f627,f391])).
% 12.04/1.93  fof(f627,plain,(
% 12.04/1.93    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl9_28),
% 12.04/1.93    inference(avatar_component_clause,[],[f625])).
% 12.04/1.93  fof(f11021,plain,(
% 12.04/1.93    spl9_2 | ~spl9_11 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30 | ~spl9_36),
% 12.04/1.93    inference(avatar_contradiction_clause,[],[f11020])).
% 12.04/1.93  fof(f11020,plain,(
% 12.04/1.93    $false | (spl9_2 | ~spl9_11 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30 | ~spl9_36)),
% 12.04/1.93    inference(subsumption_resolution,[],[f11019,f10637])).
% 12.04/1.93  fof(f10637,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | ~spl9_30)),
% 12.04/1.93    inference(global_subsumption,[],[f10633])).
% 12.04/1.93  fof(f11019,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl9_2 | ~spl9_11 | ~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.93    inference(subsumption_resolution,[],[f11018,f10155])).
% 12.04/1.93  fof(f10155,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_2 | ~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f8832,f10064])).
% 12.04/1.93  fof(f8832,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_2 | ~spl9_17)),
% 12.04/1.93    inference(forward_demodulation,[],[f8802,f105])).
% 12.04/1.93  fof(f105,plain,(
% 12.04/1.93    sK2 = sK3),
% 12.04/1.93    inference(cnf_transformation,[],[f70])).
% 12.04/1.93  fof(f8802,plain,(
% 12.04/1.93    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_2 | ~spl9_17)),
% 12.04/1.93    inference(forward_demodulation,[],[f205,f391])).
% 12.04/1.93  fof(f205,plain,(
% 12.04/1.93    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_2),
% 12.04/1.93    inference(avatar_component_clause,[],[f203])).
% 12.04/1.93  fof(f203,plain,(
% 12.04/1.93    spl9_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.04/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 12.04/1.93  fof(f11018,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_11 | ~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10632,f10564])).
% 12.04/1.93  fof(f10632,plain,(
% 12.04/1.93    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_11 | ~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.93    inference(forward_demodulation,[],[f10631,f10064])).
% 12.04/1.93  fof(f10631,plain,(
% 12.04/1.93    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_11 | ~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.93    inference(forward_demodulation,[],[f10630,f337])).
% 12.04/1.93  fof(f10630,plain,(
% 12.04/1.93    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_17 | ~spl9_27 | ~spl9_36)),
% 12.04/1.93    inference(forward_demodulation,[],[f10629,f10545])).
% 12.04/1.93  fof(f10629,plain,(
% 12.04/1.93    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10628,f391])).
% 12.04/1.93  fof(f10628,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10627,f109])).
% 12.04/1.93  fof(f10627,plain,(
% 12.04/1.93    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10626,f10064])).
% 12.04/1.93  fof(f10626,plain,(
% 12.04/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10625,f184])).
% 12.04/1.93  fof(f10625,plain,(
% 12.04/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10624,f391])).
% 12.04/1.93  fof(f10624,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10623,f10064])).
% 12.04/1.93  fof(f10623,plain,(
% 12.04/1.93    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f10622,f391])).
% 12.04/1.93  fof(f10622,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f1444,f10064])).
% 12.04/1.93  fof(f1444,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 12.04/1.93    inference(subsumption_resolution,[],[f1443,f267])).
% 12.04/1.93  fof(f267,plain,(
% 12.04/1.93    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f265,f96])).
% 12.04/1.93  fof(f265,plain,(
% 12.04/1.93    ~l1_pre_topc(sK0) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(resolution,[],[f130,f95])).
% 12.04/1.93  fof(f130,plain,(
% 12.04/1.93    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 12.04/1.93    inference(cnf_transformation,[],[f40])).
% 12.04/1.93  fof(f40,plain,(
% 12.04/1.93    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.04/1.93    inference(flattening,[],[f39])).
% 12.04/1.93  fof(f39,plain,(
% 12.04/1.93    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.04/1.93    inference(ennf_transformation,[],[f32])).
% 12.04/1.93  fof(f32,plain,(
% 12.04/1.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 12.04/1.93    inference(pure_predicate_removal,[],[f25])).
% 12.04/1.93  fof(f25,axiom,(
% 12.04/1.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 12.04/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 12.04/1.93  fof(f1443,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f1442,f592])).
% 12.04/1.93  fof(f592,plain,(
% 12.04/1.93    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(resolution,[],[f255,f144])).
% 12.04/1.93  fof(f144,plain,(
% 12.04/1.93    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 12.04/1.93    inference(cnf_transformation,[],[f49])).
% 12.04/1.93  fof(f49,plain,(
% 12.04/1.93    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 12.04/1.93    inference(ennf_transformation,[],[f31])).
% 12.04/1.93  fof(f31,plain,(
% 12.04/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 12.04/1.93    inference(pure_predicate_removal,[],[f23])).
% 12.04/1.93  fof(f23,axiom,(
% 12.04/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 12.04/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 12.04/1.93  fof(f255,plain,(
% 12.04/1.93    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 12.04/1.93    inference(resolution,[],[f110,f96])).
% 12.04/1.93  fof(f110,plain,(
% 12.04/1.93    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 12.04/1.93    inference(cnf_transformation,[],[f35])).
% 12.04/1.93  fof(f35,plain,(
% 12.04/1.93    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.04/1.93    inference(ennf_transformation,[],[f24])).
% 12.04/1.93  fof(f24,axiom,(
% 12.04/1.93    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.04/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 12.04/1.93  fof(f1442,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f1441,f97])).
% 12.04/1.93  fof(f1441,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f1440,f98])).
% 12.04/1.93  fof(f1440,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f1439,f210])).
% 12.04/1.93  fof(f210,plain,(
% 12.04/1.93    v1_funct_1(sK2)),
% 12.04/1.93    inference(forward_demodulation,[],[f102,f105])).
% 12.04/1.93  fof(f102,plain,(
% 12.04/1.93    v1_funct_1(sK3)),
% 12.04/1.93    inference(cnf_transformation,[],[f70])).
% 12.04/1.93  fof(f1439,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(subsumption_resolution,[],[f517,f209])).
% 12.04/1.93  fof(f209,plain,(
% 12.04/1.93    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.04/1.93    inference(forward_demodulation,[],[f103,f105])).
% 12.04/1.93  fof(f103,plain,(
% 12.04/1.93    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.04/1.93    inference(cnf_transformation,[],[f70])).
% 12.04/1.93  fof(f517,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.04/1.93    inference(resolution,[],[f196,f208])).
% 12.04/1.93  fof(f208,plain,(
% 12.04/1.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.04/1.93    inference(forward_demodulation,[],[f104,f105])).
% 12.04/1.93  fof(f104,plain,(
% 12.04/1.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.04/1.93    inference(cnf_transformation,[],[f70])).
% 12.04/1.93  fof(f196,plain,(
% 12.04/1.93    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(duplicate_literal_removal,[],[f176])).
% 12.04/1.93  fof(f176,plain,(
% 12.04/1.93    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(equality_resolution,[],[f131])).
% 12.04/1.93  fof(f131,plain,(
% 12.04/1.93    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(cnf_transformation,[],[f78])).
% 12.04/1.93  fof(f78,plain,(
% 12.04/1.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.04/1.93    inference(nnf_transformation,[],[f42])).
% 12.04/1.93  fof(f42,plain,(
% 12.04/1.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.04/1.93    inference(flattening,[],[f41])).
% 12.04/1.93  fof(f41,plain,(
% 12.04/1.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.04/1.93    inference(ennf_transformation,[],[f27])).
% 12.04/1.93  fof(f27,axiom,(
% 12.04/1.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.04/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 12.04/1.93  fof(f10608,plain,(
% 12.04/1.93    ~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30),
% 12.04/1.93    inference(avatar_contradiction_clause,[],[f10607])).
% 12.04/1.93  fof(f10607,plain,(
% 12.04/1.93    $false | (~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10095,f10606])).
% 12.04/1.93  fof(f10606,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10605,f95])).
% 12.04/1.93  fof(f10605,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10604,f96])).
% 12.04/1.93  fof(f10604,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10598,f10452])).
% 12.04/1.93  fof(f10598,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28 | spl9_30)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10593,f10592])).
% 12.04/1.93  fof(f10592,plain,(
% 12.04/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_17 | ~spl9_27 | spl9_30)),
% 12.04/1.93    inference(superposition,[],[f634,f10064])).
% 12.04/1.93  fof(f634,plain,(
% 12.04/1.93    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl9_30),
% 12.04/1.93    inference(avatar_component_clause,[],[f633])).
% 12.04/1.93  fof(f10593,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_27 | ~spl9_28)),
% 12.04/1.93    inference(resolution,[],[f10172,f9504])).
% 12.04/1.93  fof(f9504,plain,(
% 12.04/1.93    ( ! [X42] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1) | ~v5_pre_topc(k1_xboole_0,X42,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0) | ~l1_pre_topc(X42) | ~v2_pre_topc(X42)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.93    inference(subsumption_resolution,[],[f9503,f97])).
% 12.04/1.93  fof(f9503,plain,(
% 12.04/1.93    ( ! [X42] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1) | ~v5_pre_topc(k1_xboole_0,X42,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X42) | ~v2_pre_topc(X42)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.93    inference(subsumption_resolution,[],[f9378,f98])).
% 12.04/1.93  fof(f9378,plain,(
% 12.04/1.93    ( ! [X42] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X42),u1_pre_topc(X42)),sK1) | ~v5_pre_topc(k1_xboole_0,X42,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X42),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X42) | ~v2_pre_topc(X42)) ) | (~spl9_12 | ~spl9_17)),
% 12.04/1.93    inference(superposition,[],[f1090,f391])).
% 12.04/1.93  fof(f1090,plain,(
% 12.04/1.93    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.04/1.93    inference(subsumption_resolution,[],[f1089,f109])).
% 12.04/1.93  fof(f1089,plain,(
% 12.04/1.93    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.04/1.93    inference(subsumption_resolution,[],[f475,f348])).
% 12.04/1.93  fof(f475,plain,(
% 12.04/1.93    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(resolution,[],[f194,f109])).
% 12.04/1.93  fof(f194,plain,(
% 12.04/1.93    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(duplicate_literal_removal,[],[f178])).
% 12.04/1.93  fof(f178,plain,(
% 12.04/1.93    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(equality_resolution,[],[f133])).
% 12.04/1.93  fof(f133,plain,(
% 12.04/1.93    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.04/1.93    inference(cnf_transformation,[],[f79])).
% 12.04/1.93  fof(f10172,plain,(
% 12.04/1.93    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_27 | ~spl9_28)),
% 12.04/1.93    inference(forward_demodulation,[],[f9146,f10064])).
% 12.04/1.93  fof(f9146,plain,(
% 12.04/1.93    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_28)),
% 12.04/1.93    inference(forward_demodulation,[],[f626,f391])).
% 12.04/1.93  fof(f10095,plain,(
% 12.04/1.93    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_1 | ~spl9_17 | ~spl9_27)),
% 12.04/1.93    inference(forward_demodulation,[],[f200,f10064])).
% 12.04/1.93  fof(f200,plain,(
% 12.04/1.93    v5_pre_topc(sK2,sK0,sK1) | ~spl9_1),
% 12.04/1.93    inference(avatar_component_clause,[],[f199])).
% 12.04/1.93  fof(f10563,plain,(
% 12.04/1.93    ~spl9_17 | spl9_19 | ~spl9_32),
% 12.04/1.93    inference(avatar_contradiction_clause,[],[f10562])).
% 12.04/1.93  fof(f10562,plain,(
% 12.04/1.93    $false | (~spl9_17 | spl9_19 | ~spl9_32)),
% 12.04/1.93    inference(subsumption_resolution,[],[f10553,f10401])).
% 12.04/1.93  fof(f10401,plain,(
% 12.04/1.93    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_17 | spl9_19)),
% 12.04/1.93    inference(forward_demodulation,[],[f401,f391])).
% 12.04/1.93  fof(f401,plain,(
% 12.04/1.93    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_19),
% 12.04/1.93    inference(avatar_component_clause,[],[f400])).
% 12.04/1.93  fof(f400,plain,(
% 12.04/1.93    spl9_19 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.04/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 12.04/1.93  fof(f10553,plain,(
% 12.04/1.93    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_32),
% 12.04/1.93    inference(resolution,[],[f756,f129])).
% 12.04/1.93  fof(f129,plain,(
% 12.04/1.93    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 12.04/1.93    inference(cnf_transformation,[],[f38])).
% 12.04/1.93  fof(f38,plain,(
% 12.04/1.93    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 12.04/1.93    inference(ennf_transformation,[],[f3])).
% 12.04/1.93  fof(f3,axiom,(
% 12.04/1.93    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 12.04/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 12.04/1.93  fof(f756,plain,(
% 12.04/1.93    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl9_32),
% 12.04/1.93    inference(avatar_component_clause,[],[f754])).
% 12.04/1.93  fof(f754,plain,(
% 12.04/1.93    spl9_32 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.04/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 12.04/1.93  fof(f10543,plain,(
% 12.04/1.93    ~spl9_17 | spl9_19 | ~spl9_35),
% 12.04/1.93    inference(avatar_contradiction_clause,[],[f10542])).
% 12.56/1.93  fof(f10542,plain,(
% 12.56/1.93    $false | (~spl9_17 | spl9_19 | ~spl9_35)),
% 12.56/1.93    inference(global_subsumption,[],[f10401,f788])).
% 12.56/1.93  fof(f788,plain,(
% 12.56/1.93    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_35),
% 12.56/1.93    inference(avatar_component_clause,[],[f786])).
% 12.56/1.93  fof(f786,plain,(
% 12.56/1.93    spl9_35 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.56/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 12.56/1.93  fof(f10300,plain,(
% 12.56/1.93    ~spl9_17 | ~spl9_27 | spl9_48),
% 12.56/1.93    inference(avatar_contradiction_clause,[],[f10299])).
% 12.56/1.93  fof(f10299,plain,(
% 12.56/1.93    $false | (~spl9_17 | ~spl9_27 | spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10298,f109])).
% 12.56/1.93  fof(f10298,plain,(
% 12.56/1.93    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl9_17 | ~spl9_27 | spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f10297,f10064])).
% 12.56/1.93  fof(f10297,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl9_17 | spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f1565,f391])).
% 12.56/1.93  fof(f1565,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl9_48),
% 12.56/1.93    inference(avatar_component_clause,[],[f1563])).
% 12.56/1.93  fof(f1563,plain,(
% 12.56/1.93    spl9_48 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.56/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 12.56/1.93  fof(f10022,plain,(
% 12.56/1.93    ~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48),
% 12.56/1.93    inference(avatar_contradiction_clause,[],[f10021])).
% 12.56/1.93  fof(f10021,plain,(
% 12.56/1.93    $false | (~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10020,f95])).
% 12.56/1.93  fof(f10020,plain,(
% 12.56/1.93    ~v2_pre_topc(sK0) | (~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10019,f96])).
% 12.56/1.93  fof(f10019,plain,(
% 12.56/1.93    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10018,f8706])).
% 12.56/1.93  fof(f8706,plain,(
% 12.56/1.93    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8603,f391])).
% 12.56/1.93  fof(f8603,plain,(
% 12.56/1.93    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(superposition,[],[f100,f7160])).
% 12.56/1.93  fof(f7160,plain,(
% 12.56/1.93    k1_xboole_0 = sK2 | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f7159,f244])).
% 12.56/1.93  fof(f244,plain,(
% 12.56/1.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.56/1.93    inference(resolution,[],[f155,f109])).
% 12.56/1.93  fof(f155,plain,(
% 12.56/1.93    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 12.56/1.93    inference(cnf_transformation,[],[f91])).
% 12.56/1.93  fof(f7159,plain,(
% 12.56/1.93    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f7158,f184])).
% 12.56/1.93  fof(f7158,plain,(
% 12.56/1.93    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0),sK2) | k1_xboole_0 = sK2 | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f7157,f402])).
% 12.56/1.93  fof(f402,plain,(
% 12.56/1.93    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_19),
% 12.56/1.93    inference(avatar_component_clause,[],[f400])).
% 12.56/1.93  fof(f7157,plain,(
% 12.56/1.93    k1_xboole_0 = sK2 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f7156,f184])).
% 12.56/1.93  fof(f7156,plain,(
% 12.56/1.93    sK2 = k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f4853,f402])).
% 12.56/1.93  fof(f4853,plain,(
% 12.56/1.93    sK2 = k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),sK2) | ~spl9_48),
% 12.56/1.93    inference(resolution,[],[f4743,f150])).
% 12.56/1.93  fof(f150,plain,(
% 12.56/1.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.56/1.93    inference(cnf_transformation,[],[f86])).
% 12.56/1.93  fof(f4743,plain,(
% 12.56/1.93    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl9_48),
% 12.56/1.93    inference(resolution,[],[f1564,f155])).
% 12.56/1.93  fof(f1564,plain,(
% 12.56/1.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_48),
% 12.56/1.93    inference(avatar_component_clause,[],[f1563])).
% 12.56/1.93  fof(f10018,plain,(
% 12.56/1.93    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_1 | ~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10017,f8807])).
% 12.56/1.93  fof(f8807,plain,(
% 12.56/1.93    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_1 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f200,f7160])).
% 12.56/1.93  fof(f10017,plain,(
% 12.56/1.93    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f10011,f9288])).
% 12.56/1.93  fof(f9288,plain,(
% 12.56/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_19 | spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f634,f7160])).
% 12.56/1.93  fof(f10011,plain,(
% 12.56/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl9_12 | ~spl9_17 | ~spl9_19 | ~spl9_28 | ~spl9_48)),
% 12.56/1.93    inference(resolution,[],[f9504,f9147])).
% 12.56/1.93  fof(f9147,plain,(
% 12.56/1.93    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_19 | ~spl9_28 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f9146,f7160])).
% 12.56/1.93  fof(f9264,plain,(
% 12.56/1.93    ~spl9_19 | spl9_39 | ~spl9_48),
% 12.56/1.93    inference(avatar_contradiction_clause,[],[f9263])).
% 12.56/1.93  fof(f9263,plain,(
% 12.56/1.93    $false | (~spl9_19 | spl9_39 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f9262,f109])).
% 12.56/1.93  fof(f9262,plain,(
% 12.56/1.93    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl9_19 | spl9_39 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f1079,f7160])).
% 12.56/1.93  fof(f1079,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl9_39),
% 12.56/1.93    inference(avatar_component_clause,[],[f1077])).
% 12.56/1.93  fof(f1077,plain,(
% 12.56/1.93    spl9_39 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 12.56/1.93    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 12.56/1.93  fof(f9245,plain,(
% 12.56/1.93    spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_28 | ~spl9_30 | ~spl9_48),
% 12.56/1.93    inference(avatar_contradiction_clause,[],[f9244])).
% 12.56/1.93  fof(f9244,plain,(
% 12.56/1.93    $false | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_28 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f9243,f9147])).
% 12.56/1.93  fof(f9243,plain,(
% 12.56/1.93    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f9242,f7160])).
% 12.56/1.93  fof(f9242,plain,(
% 12.56/1.93    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f9241,f391])).
% 12.56/1.93  fof(f9241,plain,(
% 12.56/1.93    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f9240,f109])).
% 12.56/1.93  fof(f9240,plain,(
% 12.56/1.93    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f9239,f7160])).
% 12.56/1.93  fof(f9239,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f9238,f8834])).
% 12.56/1.93  fof(f8834,plain,(
% 12.56/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl9_19 | ~spl9_30 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f635,f7160])).
% 12.56/1.93  fof(f9238,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(subsumption_resolution,[],[f8988,f8833])).
% 12.56/1.93  fof(f8833,plain,(
% 12.56/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl9_2 | ~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8832,f7160])).
% 12.56/1.93  fof(f8988,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8987,f184])).
% 12.56/1.93  fof(f8987,plain,(
% 12.56/1.93    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8986,f391])).
% 12.56/1.93  fof(f8986,plain,(
% 12.56/1.93    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8985,f7160])).
% 12.56/1.93  fof(f8985,plain,(
% 12.56/1.93    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_17 | ~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f8984,f391])).
% 12.56/1.93  fof(f8984,plain,(
% 12.56/1.93    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_19 | ~spl9_48)),
% 12.56/1.93    inference(forward_demodulation,[],[f1444,f7160])).
% 12.56/1.93  fof(f9003,plain,(
% 12.56/1.93    ~spl9_17 | ~spl9_19 | spl9_28 | ~spl9_39 | ~spl9_48),
% 12.56/1.93    inference(avatar_contradiction_clause,[],[f9002])).
% 12.56/1.93  fof(f9002,plain,(
% 12.56/1.93    $false | (~spl9_17 | ~spl9_19 | spl9_28 | ~spl9_39 | ~spl9_48)),
% 12.56/1.93    inference(global_subsumption,[],[f8847,f8858])).
% 12.56/1.94  fof(f8858,plain,(
% 12.56/1.94    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | ~spl9_19 | spl9_28 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f8857,f7160])).
% 12.56/1.94  fof(f8857,plain,(
% 12.56/1.94    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_17 | spl9_28)),
% 12.56/1.94    inference(forward_demodulation,[],[f627,f391])).
% 12.56/1.94  fof(f8847,plain,(
% 12.56/1.94    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl9_19 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f7385,f7160])).
% 12.56/1.94  fof(f7385,plain,(
% 12.56/1.94    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl9_19),
% 12.56/1.94    inference(superposition,[],[f209,f402])).
% 12.56/1.94  fof(f8822,plain,(
% 12.56/1.94    ~spl9_16 | ~spl9_19 | ~spl9_31 | spl9_40 | ~spl9_48),
% 12.56/1.94    inference(avatar_contradiction_clause,[],[f8821])).
% 12.56/1.94  fof(f8821,plain,(
% 12.56/1.94    $false | (~spl9_16 | ~spl9_19 | ~spl9_31 | spl9_40 | ~spl9_48)),
% 12.56/1.94    inference(subsumption_resolution,[],[f8787,f8798])).
% 12.56/1.94  fof(f8798,plain,(
% 12.56/1.94    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl9_19 | spl9_40 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f1083,f7160])).
% 12.56/1.94  fof(f1083,plain,(
% 12.56/1.94    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | spl9_40),
% 12.56/1.94    inference(avatar_component_clause,[],[f1081])).
% 12.56/1.94  fof(f1081,plain,(
% 12.56/1.94    spl9_40 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 12.56/1.94    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 12.56/1.94  fof(f8787,plain,(
% 12.56/1.94    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl9_16 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f8786,f7160])).
% 12.56/1.94  fof(f8786,plain,(
% 12.56/1.94    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl9_16 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f8785,f402])).
% 12.56/1.94  fof(f8785,plain,(
% 12.56/1.94    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_16 | ~spl9_31 | ~spl9_48)),
% 12.56/1.94    inference(subsumption_resolution,[],[f8784,f210])).
% 12.56/1.94  fof(f8784,plain,(
% 12.56/1.94    ~v1_funct_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_16 | ~spl9_31 | ~spl9_48)),
% 12.56/1.94    inference(subsumption_resolution,[],[f4736,f873])).
% 12.56/1.94  fof(f873,plain,(
% 12.56/1.94    v1_partfun1(sK2,k1_relat_1(sK2)) | (~spl9_16 | ~spl9_31)),
% 12.56/1.94    inference(superposition,[],[f387,f641])).
% 12.56/1.94  fof(f641,plain,(
% 12.56/1.94    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl9_31),
% 12.56/1.94    inference(avatar_component_clause,[],[f639])).
% 12.56/1.94  fof(f639,plain,(
% 12.56/1.94    spl9_31 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 12.56/1.94    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 12.56/1.94  fof(f387,plain,(
% 12.56/1.94    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl9_16),
% 12.56/1.94    inference(avatar_component_clause,[],[f385])).
% 12.56/1.94  fof(f385,plain,(
% 12.56/1.94    spl9_16 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 12.56/1.94    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 12.56/1.94  fof(f4736,plain,(
% 12.56/1.94    ~v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_48),
% 12.56/1.94    inference(resolution,[],[f1564,f169])).
% 12.56/1.94  fof(f169,plain,(
% 12.56/1.94    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 12.56/1.94    inference(cnf_transformation,[],[f57])).
% 12.56/1.94  fof(f57,plain,(
% 12.56/1.94    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.56/1.94    inference(flattening,[],[f56])).
% 12.56/1.94  fof(f56,plain,(
% 12.56/1.94    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.56/1.94    inference(ennf_transformation,[],[f18])).
% 12.56/1.94  fof(f18,axiom,(
% 12.56/1.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 12.56/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 12.56/1.94  fof(f8324,plain,(
% 12.56/1.94    ~spl9_19 | ~spl9_31 | ~spl9_33 | spl9_37 | ~spl9_48),
% 12.56/1.94    inference(avatar_contradiction_clause,[],[f8323])).
% 12.56/1.94  fof(f8323,plain,(
% 12.56/1.94    $false | (~spl9_19 | ~spl9_31 | ~spl9_33 | spl9_37 | ~spl9_48)),
% 12.56/1.94    inference(subsumption_resolution,[],[f8322,f760])).
% 12.56/1.94  fof(f760,plain,(
% 12.56/1.94    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl9_33),
% 12.56/1.94    inference(avatar_component_clause,[],[f758])).
% 12.56/1.94  fof(f758,plain,(
% 12.56/1.94    spl9_33 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 12.56/1.94    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 12.56/1.94  fof(f8322,plain,(
% 12.56/1.94    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl9_19 | ~spl9_31 | spl9_37 | ~spl9_48)),
% 12.56/1.94    inference(forward_demodulation,[],[f8321,f7160])).
% 12.56/1.94  fof(f8321,plain,(
% 12.56/1.94    ~v1_xboole_0(k1_relat_1(sK2)) | (~spl9_31 | spl9_37)),
% 12.56/1.94    inference(forward_demodulation,[],[f798,f641])).
% 12.56/1.94  fof(f798,plain,(
% 12.56/1.94    ~v1_xboole_0(u1_struct_0(sK0)) | spl9_37),
% 12.56/1.94    inference(avatar_component_clause,[],[f797])).
% 12.56/1.94  fof(f797,plain,(
% 12.56/1.94    spl9_37 <=> v1_xboole_0(u1_struct_0(sK0))),
% 12.56/1.94    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 12.56/1.94  fof(f8259,plain,(
% 12.56/1.94    spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_21 | ~spl9_31 | ~spl9_37 | ~spl9_48),
% 12.56/1.94    inference(avatar_contradiction_clause,[],[f8258])).
% 12.56/1.95  fof(f8258,plain,(
% 12.56/1.95    $false | (spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_21 | ~spl9_31 | ~spl9_37 | ~spl9_48)),
% 12.56/1.95    inference(global_subsumption,[],[f1156,f3996,f7844])).
% 12.56/1.95  fof(f7844,plain,(
% 12.56/1.95    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(subsumption_resolution,[],[f7843,f334])).
% 12.56/1.95  fof(f334,plain,(
% 12.56/1.95    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl9_10),
% 12.56/1.95    inference(avatar_component_clause,[],[f333])).
% 12.56/1.95  fof(f333,plain,(
% 12.56/1.95    spl9_10 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 12.56/1.95    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 12.56/1.95  fof(f7843,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(forward_demodulation,[],[f7842,f337])).
% 12.56/1.95  fof(f7842,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(forward_demodulation,[],[f7841,f7160])).
% 12.56/1.95  fof(f7841,plain,(
% 12.56/1.95    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(subsumption_resolution,[],[f7840,f334])).
% 12.56/1.95  fof(f7840,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_11 | ~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(forward_demodulation,[],[f7839,f337])).
% 12.56/1.95  fof(f7839,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_12 | ~spl9_19 | ~spl9_31 | ~spl9_48)),
% 12.56/1.95    inference(forward_demodulation,[],[f7838,f7160])).
% 12.56/1.95  fof(f7838,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_12 | ~spl9_19 | ~spl9_31)),
% 12.56/1.95    inference(subsumption_resolution,[],[f7837,f97])).
% 12.56/1.95  fof(f7837,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_19 | ~spl9_31)),
% 12.56/1.95    inference(subsumption_resolution,[],[f7427,f98])).
% 12.56/1.95  fof(f7427,plain,(
% 12.56/1.95    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_12 | ~spl9_19 | ~spl9_31)),
% 12.56/1.95    inference(superposition,[],[f2523,f402])).
% 12.56/1.95  fof(f2523,plain,(
% 12.56/1.95    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.95    inference(subsumption_resolution,[],[f2522,f95])).
% 12.56/1.95  fof(f2522,plain,(
% 12.56/1.95    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.95    inference(subsumption_resolution,[],[f2517,f96])).
% 12.56/1.95  fof(f2517,plain,(
% 12.56/1.95    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,X0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.95    inference(superposition,[],[f1096,f641])).
% 12.56/1.95  fof(f1096,plain,(
% 12.56/1.95    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.56/1.95    inference(subsumption_resolution,[],[f1095,f109])).
% 12.56/1.95  fof(f1095,plain,(
% 12.56/1.95    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.56/1.95    inference(subsumption_resolution,[],[f534,f348])).
% 12.56/1.95  fof(f534,plain,(
% 12.56/1.95    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.56/1.95    inference(resolution,[],[f197,f109])).
% 12.56/1.95  fof(f197,plain,(
% 12.56/1.95    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.56/1.95    inference(duplicate_literal_removal,[],[f175])).
% 12.56/1.95  fof(f175,plain,(
% 12.56/1.95    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.56/1.95    inference(equality_resolution,[],[f132])).
% 12.56/1.95  fof(f132,plain,(
% 12.56/1.95    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.56/1.95    inference(cnf_transformation,[],[f78])).
% 12.56/1.95  fof(f3996,plain,(
% 12.56/1.95    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_21 | ~spl9_31 | ~spl9_37)),
% 12.56/1.95    inference(forward_demodulation,[],[f507,f1622])).
% 12.56/1.95  fof(f1622,plain,(
% 12.56/1.95    k1_xboole_0 = sK2 | (~spl9_31 | ~spl9_37)),
% 12.56/1.95    inference(resolution,[],[f1573,f129])).
% 12.56/1.95  fof(f1573,plain,(
% 12.56/1.95    v1_xboole_0(sK2) | (~spl9_31 | ~spl9_37)),
% 12.56/1.95    inference(global_subsumption,[],[f1127])).
% 12.56/1.96  fof(f1127,plain,(
% 12.56/1.96    v1_xboole_0(sK2) | (~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(global_subsumption,[],[f818,f1110])).
% 12.56/1.96  fof(f1110,plain,(
% 12.56/1.96    ~v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(sK2) | ~spl9_31),
% 12.56/1.96    inference(forward_demodulation,[],[f269,f641])).
% 12.56/1.96  fof(f269,plain,(
% 12.56/1.96    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(sK0))),
% 12.56/1.96    inference(resolution,[],[f141,f101])).
% 12.56/1.96  fof(f101,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 12.56/1.96    inference(cnf_transformation,[],[f70])).
% 12.56/1.96  fof(f141,plain,(
% 12.56/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 12.56/1.96    inference(cnf_transformation,[],[f46])).
% 12.56/1.96  fof(f46,plain,(
% 12.56/1.96    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 12.56/1.96    inference(ennf_transformation,[],[f13])).
% 12.56/1.96  fof(f13,axiom,(
% 12.56/1.96    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 12.56/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 12.56/1.96  fof(f818,plain,(
% 12.56/1.96    v1_xboole_0(k1_relat_1(sK2)) | (~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f799,f641])).
% 12.56/1.96  fof(f799,plain,(
% 12.56/1.96    v1_xboole_0(u1_struct_0(sK0)) | ~spl9_37),
% 12.56/1.96    inference(avatar_component_clause,[],[f797])).
% 12.56/1.96  fof(f507,plain,(
% 12.56/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_21),
% 12.56/1.96    inference(avatar_component_clause,[],[f505])).
% 12.56/1.96  fof(f505,plain,(
% 12.56/1.96    spl9_21 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.56/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 12.56/1.96  fof(f1156,plain,(
% 12.56/1.96    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl9_1 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(superposition,[],[f201,f1140])).
% 12.56/1.96  fof(f1140,plain,(
% 12.56/1.96    k1_xboole_0 = sK2 | (~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(resolution,[],[f1127,f129])).
% 12.56/1.96  fof(f6319,plain,(
% 12.56/1.96    spl9_22 | ~spl9_30 | ~spl9_31),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f6318])).
% 12.56/1.96  fof(f6318,plain,(
% 12.56/1.96    $false | (spl9_22 | ~spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(global_subsumption,[],[f553,f6317])).
% 12.56/1.96  fof(f6317,plain,(
% 12.56/1.96    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(forward_demodulation,[],[f635,f641])).
% 12.56/1.96  fof(f553,plain,(
% 12.56/1.96    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | spl9_22),
% 12.56/1.96    inference(avatar_component_clause,[],[f552])).
% 12.56/1.96  fof(f552,plain,(
% 12.56/1.96    spl9_22 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 12.56/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 12.56/1.96  fof(f6267,plain,(
% 12.56/1.96    ~spl9_1 | spl9_19 | ~spl9_29 | spl9_30 | ~spl9_31),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f6266])).
% 12.56/1.96  fof(f6266,plain,(
% 12.56/1.96    $false | (~spl9_1 | spl9_19 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6265,f863])).
% 12.56/1.96  fof(f863,plain,(
% 12.56/1.96    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f100,f641])).
% 12.56/1.96  fof(f6265,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl9_1 | spl9_19 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(forward_demodulation,[],[f6264,f4630])).
% 12.56/1.96  fof(f4630,plain,(
% 12.56/1.96    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (spl9_19 | ~spl9_31)),
% 12.56/1.96    inference(forward_demodulation,[],[f4103,f1965])).
% 12.56/1.96  fof(f1965,plain,(
% 12.56/1.96    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f312,f641])).
% 12.56/1.96  fof(f312,plain,(
% 12.56/1.96    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 12.56/1.96    inference(resolution,[],[f161,f208])).
% 12.56/1.96  fof(f4103,plain,(
% 12.56/1.96    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (spl9_19 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f3444,f401])).
% 12.56/1.96  fof(f3444,plain,(
% 12.56/1.96    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_31),
% 12.56/1.96    inference(subsumption_resolution,[],[f3380,f866])).
% 12.56/1.96  fof(f866,plain,(
% 12.56/1.96    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f209,f641])).
% 12.56/1.96  fof(f3380,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_31),
% 12.56/1.96    inference(resolution,[],[f865,f162])).
% 12.56/1.96  fof(f162,plain,(
% 12.56/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 12.56/1.96    inference(cnf_transformation,[],[f94])).
% 12.56/1.96  fof(f865,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f208,f641])).
% 12.56/1.96  fof(f6264,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6263,f97])).
% 12.56/1.96  fof(f6263,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6262,f98])).
% 12.56/1.96  fof(f6262,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6261,f863])).
% 12.56/1.96  fof(f6261,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6260,f864])).
% 12.56/1.96  fof(f864,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f101,f641])).
% 12.56/1.96  fof(f6260,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6259,f210])).
% 12.56/1.96  fof(f6259,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6258,f3911])).
% 12.56/1.96  fof(f3911,plain,(
% 12.56/1.96    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (spl9_30 | ~spl9_31)),
% 12.56/1.96    inference(forward_demodulation,[],[f634,f641])).
% 12.56/1.96  fof(f6258,plain,(
% 12.56/1.96    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_29 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f6191,f200])).
% 12.56/1.96  fof(f6191,plain,(
% 12.56/1.96    ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_29 | ~spl9_31)),
% 12.56/1.96    inference(resolution,[],[f937,f1462])).
% 12.56/1.96  fof(f1462,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl9_29 | ~spl9_31)),
% 12.56/1.96    inference(forward_demodulation,[],[f630,f641])).
% 12.56/1.96  fof(f630,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl9_29),
% 12.56/1.96    inference(avatar_component_clause,[],[f629])).
% 12.56/1.96  fof(f629,plain,(
% 12.56/1.96    spl9_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 12.56/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 12.56/1.96  fof(f937,plain,(
% 12.56/1.96    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)))) | ~v5_pre_topc(X3,sK0,X4) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4)) ) | ~spl9_31),
% 12.56/1.96    inference(subsumption_resolution,[],[f936,f95])).
% 12.56/1.96  fof(f936,plain,(
% 12.56/1.96    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)))) | ~v5_pre_topc(X3,sK0,X4) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v2_pre_topc(sK0)) ) | ~spl9_31),
% 12.56/1.96    inference(subsumption_resolution,[],[f891,f96])).
% 12.56/1.96  fof(f891,plain,(
% 12.56/1.96    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)))) | ~v5_pre_topc(X3,sK0,X4) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X4) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X4)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl9_31),
% 12.56/1.96    inference(superposition,[],[f194,f641])).
% 12.56/1.96  fof(f4502,plain,(
% 12.56/1.96    ~spl9_31 | spl9_37 | spl9_38 | ~spl9_39),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f4501])).
% 12.56/1.96  fof(f4501,plain,(
% 12.56/1.96    $false | (~spl9_31 | spl9_37 | spl9_38 | ~spl9_39)),
% 12.56/1.96    inference(global_subsumption,[],[f1942,f1107,f4500])).
% 12.56/1.96  fof(f4500,plain,(
% 12.56/1.96    ~v1_xboole_0(k1_relat_1(sK2)) | (~spl9_31 | spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f798,f641])).
% 12.56/1.96  fof(f1107,plain,(
% 12.56/1.96    v1_xboole_0(k1_relat_1(sK2)) | ~v1_xboole_0(sK2) | (~spl9_31 | spl9_38)),
% 12.56/1.96    inference(forward_demodulation,[],[f1106,f641])).
% 12.56/1.96  fof(f1106,plain,(
% 12.56/1.96    ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(sK0)) | spl9_38),
% 12.56/1.96    inference(subsumption_resolution,[],[f763,f802])).
% 12.56/1.96  fof(f802,plain,(
% 12.56/1.96    ~v1_xboole_0(u1_struct_0(sK1)) | spl9_38),
% 12.56/1.96    inference(avatar_component_clause,[],[f801])).
% 12.56/1.96  fof(f801,plain,(
% 12.56/1.96    spl9_38 <=> v1_xboole_0(u1_struct_0(sK1))),
% 12.56/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 12.56/1.96  fof(f763,plain,(
% 12.56/1.96    ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 12.56/1.96    inference(subsumption_resolution,[],[f762,f210])).
% 12.56/1.96  fof(f762,plain,(
% 12.56/1.96    ~v1_funct_1(sK2) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 12.56/1.96    inference(subsumption_resolution,[],[f372,f100])).
% 12.56/1.96  fof(f372,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 12.56/1.96    inference(resolution,[],[f146,f101])).
% 12.56/1.96  fof(f146,plain,(
% 12.56/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 12.56/1.96    inference(cnf_transformation,[],[f51])).
% 12.56/1.96  fof(f51,plain,(
% 12.56/1.96    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 12.56/1.96    inference(flattening,[],[f50])).
% 12.56/1.96  fof(f50,plain,(
% 12.56/1.96    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 12.56/1.96    inference(ennf_transformation,[],[f19])).
% 12.56/1.96  fof(f19,axiom,(
% 12.56/1.96    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 12.56/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 12.56/1.96  fof(f1942,plain,(
% 12.56/1.96    v1_xboole_0(sK2) | ~spl9_39),
% 12.56/1.96    inference(resolution,[],[f283,f1078])).
% 12.56/1.96  fof(f1078,plain,(
% 12.56/1.96    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl9_39),
% 12.56/1.96    inference(avatar_component_clause,[],[f1077])).
% 12.56/1.96  fof(f283,plain,(
% 12.56/1.96    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X3)) )),
% 12.56/1.96    inference(subsumption_resolution,[],[f273,f108])).
% 12.56/1.96  fof(f108,plain,(
% 12.56/1.96    v1_xboole_0(k1_xboole_0)),
% 12.56/1.96    inference(cnf_transformation,[],[f2])).
% 12.56/1.96  fof(f2,axiom,(
% 12.56/1.96    v1_xboole_0(k1_xboole_0)),
% 12.56/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 12.56/1.96  fof(f273,plain,(
% 12.56/1.96    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X3) | ~v1_xboole_0(k1_xboole_0)) )),
% 12.56/1.96    inference(superposition,[],[f141,f185])).
% 12.56/1.96  fof(f3995,plain,(
% 12.56/1.96    ~spl9_10 | ~spl9_11 | ~spl9_31 | ~spl9_37 | spl9_49),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f3994])).
% 12.56/1.96  fof(f3994,plain,(
% 12.56/1.96    $false | (~spl9_10 | ~spl9_11 | ~spl9_31 | ~spl9_37 | spl9_49)),
% 12.56/1.96    inference(subsumption_resolution,[],[f3993,f334])).
% 12.56/1.96  fof(f3993,plain,(
% 12.56/1.96    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_11 | ~spl9_31 | ~spl9_37 | spl9_49)),
% 12.56/1.96    inference(forward_demodulation,[],[f3992,f337])).
% 12.56/1.96  fof(f3992,plain,(
% 12.56/1.96    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_31 | ~spl9_37 | spl9_49)),
% 12.56/1.96    inference(forward_demodulation,[],[f1569,f1622])).
% 12.56/1.96  fof(f1569,plain,(
% 12.56/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl9_49),
% 12.56/1.96    inference(avatar_component_clause,[],[f1567])).
% 12.56/1.96  fof(f1567,plain,(
% 12.56/1.96    spl9_49 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.56/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 12.56/1.96  fof(f3908,plain,(
% 12.56/1.96    ~spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_21 | ~spl9_31 | ~spl9_37),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f3907])).
% 12.56/1.96  fof(f3907,plain,(
% 12.56/1.96    $false | (~spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | spl9_21 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(global_subsumption,[],[f3551,f3423])).
% 12.56/1.96  fof(f3423,plain,(
% 12.56/1.96    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(subsumption_resolution,[],[f3422,f97])).
% 12.56/1.96  fof(f3422,plain,(
% 12.56/1.96    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(subsumption_resolution,[],[f3417,f98])).
% 12.56/1.96  fof(f3417,plain,(
% 12.56/1.96    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl9_1 | ~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(resolution,[],[f2500,f1762])).
% 12.56/1.96  fof(f1762,plain,(
% 12.56/1.96    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl9_1 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(superposition,[],[f200,f1622])).
% 12.56/1.96  fof(f2500,plain,(
% 12.56/1.96    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,sK0,X0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(subsumption_resolution,[],[f2499,f334])).
% 12.56/1.96  fof(f2499,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f2498,f337])).
% 12.56/1.96  fof(f2498,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f2497,f1622])).
% 12.56/1.96  fof(f2497,plain,(
% 12.56/1.96    ( ! [X0] : (v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(subsumption_resolution,[],[f2496,f334])).
% 12.56/1.96  fof(f2496,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_11 | ~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f2495,f337])).
% 12.56/1.96  fof(f2495,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_12 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f2494,f1622])).
% 12.56/1.96  fof(f2494,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f2493,f95])).
% 12.56/1.96  fof(f2493,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.96    inference(subsumption_resolution,[],[f2488,f96])).
% 12.56/1.96  fof(f2488,plain,(
% 12.56/1.96    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl9_12 | ~spl9_31)),
% 12.56/1.96    inference(superposition,[],[f1094,f641])).
% 12.56/1.96  fof(f1094,plain,(
% 12.56/1.96    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(k1_xboole_0,X0,X1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.56/1.96    inference(subsumption_resolution,[],[f1093,f109])).
% 12.56/1.96  fof(f1093,plain,(
% 12.56/1.96    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl9_12),
% 12.56/1.96    inference(subsumption_resolution,[],[f518,f348])).
% 12.56/1.96  fof(f518,plain,(
% 12.56/1.96    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,X0,X1) | v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.56/1.96    inference(resolution,[],[f196,f109])).
% 12.56/1.96  fof(f3551,plain,(
% 12.56/1.96    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_21 | ~spl9_31 | ~spl9_37)),
% 12.56/1.96    inference(forward_demodulation,[],[f506,f1622])).
% 12.56/1.96  fof(f506,plain,(
% 12.56/1.96    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl9_21),
% 12.56/1.96    inference(avatar_component_clause,[],[f505])).
% 12.56/1.96  fof(f1588,plain,(
% 12.56/1.96    ~spl9_19 | ~spl9_31 | spl9_48),
% 12.56/1.96    inference(avatar_contradiction_clause,[],[f1587])).
% 12.56/1.96  fof(f1587,plain,(
% 12.56/1.96    $false | (~spl9_19 | ~spl9_31 | spl9_48)),
% 12.56/1.96    inference(global_subsumption,[],[f903,f1583])).
% 12.56/1.96  fof(f1583,plain,(
% 12.56/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl9_19 | ~spl9_31 | spl9_48)),
% 12.56/1.96    inference(forward_demodulation,[],[f1582,f184])).
% 12.56/1.96  fof(f1582,plain,(
% 12.56/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl9_19 | ~spl9_31 | spl9_48)),
% 12.56/1.96    inference(forward_demodulation,[],[f1565,f1574])).
% 12.80/1.96  fof(f1574,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(global_subsumption,[],[f402])).
% 12.80/1.96  fof(f903,plain,(
% 12.80/1.96    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f902,f184])).
% 12.80/1.96  fof(f902,plain,(
% 12.80/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f865,f402])).
% 12.80/1.96  fof(f1570,plain,(
% 12.80/1.96    ~spl9_48 | ~spl9_49 | spl9_2 | ~spl9_21 | ~spl9_31),
% 12.80/1.96    inference(avatar_split_clause,[],[f1561,f639,f505,f203,f1567,f1563])).
% 12.80/1.96  fof(f1561,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl9_2 | ~spl9_21 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1473,f1465])).
% 12.80/1.96  fof(f1465,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_2 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1464,f105])).
% 12.80/1.96  fof(f1464,plain,(
% 12.80/1.96    ~v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl9_2 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f205,f641])).
% 12.80/1.96  fof(f1473,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_21 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1472,f641])).
% 12.80/1.96  fof(f1472,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_21 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1461,f641])).
% 12.80/1.96  fof(f1461,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_21 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1460,f641])).
% 12.80/1.96  fof(f1460,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1459,f95])).
% 12.80/1.96  fof(f1459,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1458,f96])).
% 12.80/1.96  fof(f1458,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1457,f268])).
% 12.80/1.96  fof(f268,plain,(
% 12.80/1.96    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.80/1.96    inference(subsumption_resolution,[],[f266,f98])).
% 12.80/1.96  fof(f266,plain,(
% 12.80/1.96    ~l1_pre_topc(sK1) | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.80/1.96    inference(resolution,[],[f130,f97])).
% 12.80/1.96  fof(f1457,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1456,f1046])).
% 12.80/1.96  fof(f1046,plain,(
% 12.80/1.96    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.80/1.96    inference(resolution,[],[f256,f144])).
% 12.80/1.96  fof(f256,plain,(
% 12.80/1.96    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 12.80/1.96    inference(resolution,[],[f110,f98])).
% 12.80/1.96  fof(f1456,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1455,f210])).
% 12.80/1.96  fof(f1455,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f1454,f209])).
% 12.80/1.96  fof(f1454,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_21),
% 12.80/1.96    inference(subsumption_resolution,[],[f474,f507])).
% 12.80/1.96  fof(f474,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 12.80/1.96    inference(resolution,[],[f194,f208])).
% 12.80/1.96  fof(f1557,plain,(
% 12.80/1.96    spl9_2 | ~spl9_22 | ~spl9_28 | ~spl9_29 | ~spl9_31),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1556])).
% 12.80/1.96  fof(f1556,plain,(
% 12.80/1.96    $false | (spl9_2 | ~spl9_22 | ~spl9_28 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(global_subsumption,[],[f1298,f1476,f1462,f1465])).
% 12.80/1.96  fof(f1476,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_22 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1448,f641])).
% 12.80/1.96  fof(f1448,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_22 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1447,f641])).
% 12.80/1.96  fof(f1447,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_22 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1446,f641])).
% 12.80/1.96  fof(f1446,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_22 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1445,f554])).
% 12.80/1.96  fof(f554,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~spl9_22),
% 12.80/1.96    inference(avatar_component_clause,[],[f552])).
% 12.80/1.96  fof(f1445,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl9_31),
% 12.80/1.96    inference(forward_demodulation,[],[f1444,f641])).
% 12.80/1.96  fof(f1298,plain,(
% 12.80/1.96    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl9_28 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f626,f641])).
% 12.80/1.96  fof(f1430,plain,(
% 12.80/1.96    spl9_19 | spl9_29 | ~spl9_31),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1429])).
% 12.80/1.96  fof(f1429,plain,(
% 12.80/1.96    $false | (spl9_19 | spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1428,f864])).
% 12.80/1.96  fof(f1428,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (spl9_19 | spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1427,f1189])).
% 12.80/1.96  fof(f1189,plain,(
% 12.80/1.96    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(global_subsumption,[],[f401,f1188])).
% 12.80/1.96  fof(f1188,plain,(
% 12.80/1.96    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_31),
% 12.80/1.96    inference(forward_demodulation,[],[f1187,f641])).
% 12.80/1.96  fof(f1187,plain,(
% 12.80/1.96    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.80/1.96    inference(forward_demodulation,[],[f416,f312])).
% 12.80/1.96  fof(f416,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 12.80/1.96    inference(subsumption_resolution,[],[f409,f209])).
% 12.80/1.96  fof(f409,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 12.80/1.96    inference(resolution,[],[f162,f208])).
% 12.80/1.96  fof(f1427,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f631,f641])).
% 12.80/1.96  fof(f631,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl9_29),
% 12.80/1.96    inference(avatar_component_clause,[],[f629])).
% 12.80/1.96  fof(f1394,plain,(
% 12.80/1.96    spl9_1 | spl9_19 | ~spl9_22 | ~spl9_29 | ~spl9_31),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1393])).
% 12.80/1.96  fof(f1393,plain,(
% 12.80/1.96    $false | (spl9_1 | spl9_19 | ~spl9_22 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1392,f863])).
% 12.80/1.96  fof(f1392,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (spl9_1 | spl9_19 | ~spl9_22 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1391,f1189])).
% 12.80/1.96  fof(f1391,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_1 | ~spl9_22 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1390,f641])).
% 12.80/1.96  fof(f1390,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_1 | ~spl9_22 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1389,f554])).
% 12.80/1.96  fof(f1389,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_1 | ~spl9_29 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1388,f641])).
% 12.80/1.96  fof(f1388,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1387,f95])).
% 12.80/1.96  fof(f1387,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1386,f96])).
% 12.80/1.96  fof(f1386,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1385,f97])).
% 12.80/1.96  fof(f1385,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1384,f98])).
% 12.80/1.96  fof(f1384,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1383,f100])).
% 12.80/1.96  fof(f1383,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1382,f101])).
% 12.80/1.96  fof(f1382,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1381,f210])).
% 12.80/1.96  fof(f1381,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl9_1 | ~spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1364,f201])).
% 12.80/1.96  fof(f1364,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_29),
% 12.80/1.96    inference(resolution,[],[f630,f195])).
% 12.80/1.96  fof(f1297,plain,(
% 12.80/1.96    spl9_19 | spl9_28 | ~spl9_31),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1296])).
% 12.80/1.96  fof(f1296,plain,(
% 12.80/1.96    $false | (spl9_19 | spl9_28 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1295,f863])).
% 12.80/1.96  fof(f1295,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (spl9_19 | spl9_28 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1294,f1189])).
% 12.80/1.96  fof(f1294,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl9_28 | ~spl9_31)),
% 12.80/1.96    inference(superposition,[],[f627,f641])).
% 12.80/1.96  fof(f1196,plain,(
% 12.80/1.96    spl9_11 | ~spl9_33),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1195])).
% 12.80/1.96  fof(f1195,plain,(
% 12.80/1.96    $false | (spl9_11 | ~spl9_33)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1194,f338])).
% 12.80/1.96  fof(f338,plain,(
% 12.80/1.96    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl9_11),
% 12.80/1.96    inference(avatar_component_clause,[],[f336])).
% 12.80/1.96  fof(f1194,plain,(
% 12.80/1.96    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_33),
% 12.80/1.96    inference(resolution,[],[f760,f129])).
% 12.80/1.96  fof(f1137,plain,(
% 12.80/1.96    ~spl9_19 | ~spl9_31 | spl9_39),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1136])).
% 12.80/1.96  fof(f1136,plain,(
% 12.80/1.96    $false | (~spl9_19 | ~spl9_31 | spl9_39)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1079,f903])).
% 12.80/1.96  fof(f1135,plain,(
% 12.80/1.96    spl9_21 | ~spl9_40 | ~spl9_2 | ~spl9_19 | ~spl9_31),
% 12.80/1.96    inference(avatar_split_clause,[],[f1134,f639,f400,f203,f1081,f505])).
% 12.80/1.96  fof(f1134,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1133,f641])).
% 12.80/1.96  fof(f1133,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl9_2 | ~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(forward_demodulation,[],[f1132,f402])).
% 12.80/1.96  fof(f1132,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_2 | ~spl9_19 | ~spl9_31)),
% 12.80/1.96    inference(subsumption_resolution,[],[f1131,f903])).
% 12.80/1.96  fof(f1131,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_2 | ~spl9_19)),
% 12.80/1.96    inference(forward_demodulation,[],[f1130,f184])).
% 12.80/1.96  fof(f1130,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl9_2 | ~spl9_19)),
% 12.80/1.96    inference(forward_demodulation,[],[f1129,f402])).
% 12.80/1.96  fof(f1129,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f495,f1046])).
% 12.80/1.96  fof(f495,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f494,f95])).
% 12.80/1.96  fof(f494,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f493,f96])).
% 12.80/1.96  fof(f493,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f492,f268])).
% 12.80/1.96  fof(f492,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f491,f210])).
% 12.80/1.96  fof(f491,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f490,f209])).
% 12.80/1.96  fof(f490,plain,(
% 12.80/1.96    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f486,f218])).
% 12.80/1.96  fof(f218,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_2),
% 12.80/1.96    inference(forward_demodulation,[],[f204,f105])).
% 12.80/1.96  fof(f204,plain,(
% 12.80/1.96    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl9_2),
% 12.80/1.96    inference(avatar_component_clause,[],[f203])).
% 12.80/1.96  fof(f486,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 12.80/1.96    inference(resolution,[],[f195,f208])).
% 12.80/1.96  fof(f1109,plain,(
% 12.80/1.96    spl9_4 | ~spl9_19 | ~spl9_31 | spl9_38),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1108])).
% 12.80/1.96  fof(f1108,plain,(
% 12.80/1.96    $false | (spl9_4 | ~spl9_19 | ~spl9_31 | spl9_38)),
% 12.80/1.96    inference(global_subsumption,[],[f233,f1101])).
% 12.80/1.96  fof(f1101,plain,(
% 12.80/1.96    v1_xboole_0(sK2) | ~spl9_19),
% 12.80/1.96    inference(subsumption_resolution,[],[f1100,f108])).
% 12.80/1.96  fof(f1100,plain,(
% 12.80/1.96    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2) | ~spl9_19),
% 12.80/1.96    inference(forward_demodulation,[],[f285,f402])).
% 12.80/1.96  fof(f285,plain,(
% 12.80/1.96    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.80/1.96    inference(resolution,[],[f142,f208])).
% 12.80/1.96  fof(f142,plain,(
% 12.80/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 12.80/1.96    inference(cnf_transformation,[],[f47])).
% 12.80/1.96  fof(f47,plain,(
% 12.80/1.96    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 12.80/1.96    inference(ennf_transformation,[],[f14])).
% 12.80/1.96  fof(f14,axiom,(
% 12.80/1.96    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 12.80/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 12.80/1.96  fof(f233,plain,(
% 12.80/1.96    ~v1_xboole_0(sK2) | spl9_4),
% 12.80/1.96    inference(avatar_component_clause,[],[f232])).
% 12.80/1.96  fof(f232,plain,(
% 12.80/1.96    spl9_4 <=> v1_xboole_0(sK2)),
% 12.80/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 12.80/1.96  fof(f1099,plain,(
% 12.80/1.96    spl9_4 | spl9_17 | ~spl9_31 | ~spl9_37),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f1098])).
% 12.80/1.96  fof(f1098,plain,(
% 12.80/1.96    $false | (spl9_4 | spl9_17 | ~spl9_31 | ~spl9_37)),
% 12.80/1.96    inference(global_subsumption,[],[f448,f818])).
% 12.80/1.96  fof(f448,plain,(
% 12.80/1.96    ~v1_xboole_0(k1_relat_1(sK2)) | (spl9_4 | spl9_17)),
% 12.80/1.96    inference(superposition,[],[f274,f415])).
% 12.80/1.96  fof(f415,plain,(
% 12.80/1.96    u1_struct_0(sK0) = k1_relat_1(sK2) | spl9_17),
% 12.80/1.96    inference(forward_demodulation,[],[f414,f311])).
% 12.80/1.96  fof(f311,plain,(
% 12.80/1.96    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 12.80/1.96    inference(resolution,[],[f161,f101])).
% 12.80/1.96  fof(f414,plain,(
% 12.80/1.96    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | spl9_17),
% 12.80/1.96    inference(subsumption_resolution,[],[f413,f390])).
% 12.80/1.96  fof(f390,plain,(
% 12.80/1.96    k1_xboole_0 != u1_struct_0(sK1) | spl9_17),
% 12.80/1.96    inference(avatar_component_clause,[],[f389])).
% 12.80/1.96  fof(f413,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 12.80/1.96    inference(subsumption_resolution,[],[f408,f100])).
% 12.80/1.96  fof(f408,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 12.80/1.96    inference(resolution,[],[f162,f101])).
% 12.80/1.96  fof(f274,plain,(
% 12.80/1.96    ~v1_xboole_0(u1_struct_0(sK0)) | spl9_4),
% 12.80/1.96    inference(subsumption_resolution,[],[f269,f233])).
% 12.80/1.96  fof(f845,plain,(
% 12.80/1.96    ~spl9_4 | spl9_12),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f844])).
% 12.80/1.96  fof(f844,plain,(
% 12.80/1.96    $false | (~spl9_4 | spl9_12)),
% 12.80/1.96    inference(subsumption_resolution,[],[f832,f349])).
% 12.80/1.96  fof(f349,plain,(
% 12.80/1.96    ~v1_funct_1(k1_xboole_0) | spl9_12),
% 12.80/1.96    inference(avatar_component_clause,[],[f347])).
% 12.80/1.96  fof(f832,plain,(
% 12.80/1.96    v1_funct_1(k1_xboole_0) | ~spl9_4),
% 12.80/1.96    inference(superposition,[],[f210,f812])).
% 12.80/1.96  fof(f812,plain,(
% 12.80/1.96    k1_xboole_0 = sK2 | ~spl9_4),
% 12.80/1.96    inference(resolution,[],[f234,f129])).
% 12.80/1.96  fof(f234,plain,(
% 12.80/1.96    v1_xboole_0(sK2) | ~spl9_4),
% 12.80/1.96    inference(avatar_component_clause,[],[f232])).
% 12.80/1.96  fof(f821,plain,(
% 12.80/1.96    ~spl9_4 | ~spl9_31 | spl9_33 | ~spl9_37),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f820])).
% 12.80/1.96  fof(f820,plain,(
% 12.80/1.96    $false | (~spl9_4 | ~spl9_31 | spl9_33 | ~spl9_37)),
% 12.80/1.96    inference(subsumption_resolution,[],[f819,f759])).
% 12.80/1.96  fof(f759,plain,(
% 12.80/1.96    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | spl9_33),
% 12.80/1.96    inference(avatar_component_clause,[],[f758])).
% 12.80/1.96  fof(f819,plain,(
% 12.80/1.96    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl9_4 | ~spl9_31 | ~spl9_37)),
% 12.80/1.96    inference(forward_demodulation,[],[f818,f812])).
% 12.80/1.96  fof(f817,plain,(
% 12.80/1.96    spl9_17 | ~spl9_38),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f816])).
% 12.80/1.96  fof(f816,plain,(
% 12.80/1.96    $false | (spl9_17 | ~spl9_38)),
% 12.80/1.96    inference(subsumption_resolution,[],[f815,f390])).
% 12.80/1.96  fof(f815,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(sK1) | ~spl9_38),
% 12.80/1.96    inference(resolution,[],[f803,f129])).
% 12.80/1.96  fof(f803,plain,(
% 12.80/1.96    v1_xboole_0(u1_struct_0(sK1)) | ~spl9_38),
% 12.80/1.96    inference(avatar_component_clause,[],[f801])).
% 12.80/1.96  fof(f793,plain,(
% 12.80/1.96    spl9_35 | spl9_36 | ~spl9_17 | ~spl9_27),
% 12.80/1.96    inference(avatar_split_clause,[],[f784,f617,f389,f790,f786])).
% 12.80/1.96  fof(f784,plain,(
% 12.80/1.96    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f783,f654])).
% 12.80/1.96  fof(f654,plain,(
% 12.80/1.96    k1_xboole_0 = sK2 | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f653,f184])).
% 12.80/1.96  fof(f653,plain,(
% 12.80/1.96    sK2 = k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0) | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f619,f391])).
% 12.80/1.96  fof(f783,plain,(
% 12.80/1.96    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl9_17),
% 12.80/1.96    inference(forward_demodulation,[],[f782,f312])).
% 12.80/1.96  fof(f782,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl9_17),
% 12.80/1.96    inference(forward_demodulation,[],[f416,f391])).
% 12.80/1.96  fof(f761,plain,(
% 12.80/1.96    spl9_32 | spl9_33 | ~spl9_17 | spl9_19 | ~spl9_27),
% 12.80/1.96    inference(avatar_split_clause,[],[f752,f617,f400,f389,f758,f754])).
% 12.80/1.96  fof(f752,plain,(
% 12.80/1.96    v1_xboole_0(k1_relat_1(k1_xboole_0)) | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_17 | spl9_19 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f751,f654])).
% 12.80/1.96  fof(f751,plain,(
% 12.80/1.96    v1_xboole_0(k1_relat_1(sK2)) | v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl9_17 | spl9_19 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f750,f418])).
% 12.80/1.96  fof(f418,plain,(
% 12.80/1.96    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | spl9_19),
% 12.80/1.96    inference(forward_demodulation,[],[f417,f312])).
% 12.80/1.96  fof(f417,plain,(
% 12.80/1.96    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | spl9_19),
% 12.80/1.96    inference(subsumption_resolution,[],[f416,f401])).
% 12.80/1.96  fof(f750,plain,(
% 12.80/1.96    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f749,f391])).
% 12.80/1.96  fof(f749,plain,(
% 12.80/1.96    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(subsumption_resolution,[],[f748,f108])).
% 12.80/1.96  fof(f748,plain,(
% 12.80/1.96    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl9_17 | ~spl9_27)),
% 12.80/1.96    inference(forward_demodulation,[],[f747,f654])).
% 12.80/1.96  fof(f747,plain,(
% 12.80/1.96    ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.80/1.96    inference(subsumption_resolution,[],[f746,f210])).
% 12.80/1.96  fof(f746,plain,(
% 12.80/1.96    ~v1_funct_1(sK2) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.80/1.96    inference(subsumption_resolution,[],[f373,f209])).
% 12.80/1.96  fof(f373,plain,(
% 12.80/1.96    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~v1_xboole_0(sK2) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.80/1.96    inference(resolution,[],[f146,f208])).
% 12.80/1.96  fof(f707,plain,(
% 12.80/1.96    spl9_4 | ~spl9_17),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f706])).
% 12.80/1.96  fof(f706,plain,(
% 12.80/1.96    $false | (spl9_4 | ~spl9_17)),
% 12.80/1.96    inference(subsumption_resolution,[],[f668,f108])).
% 12.80/1.96  fof(f668,plain,(
% 12.80/1.96    ~v1_xboole_0(k1_xboole_0) | (spl9_4 | ~spl9_17)),
% 12.80/1.96    inference(superposition,[],[f532,f391])).
% 12.80/1.96  fof(f532,plain,(
% 12.80/1.96    ~v1_xboole_0(u1_struct_0(sK1)) | spl9_4),
% 12.80/1.96    inference(subsumption_resolution,[],[f284,f233])).
% 12.80/1.96  fof(f284,plain,(
% 12.80/1.96    v1_xboole_0(sK2) | ~v1_xboole_0(u1_struct_0(sK1))),
% 12.80/1.96    inference(resolution,[],[f142,f101])).
% 12.80/1.96  fof(f697,plain,(
% 12.80/1.96    ~spl9_17 | spl9_29),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f696])).
% 12.80/1.96  fof(f696,plain,(
% 12.80/1.96    $false | (~spl9_17 | spl9_29)),
% 12.80/1.96    inference(subsumption_resolution,[],[f695,f644])).
% 12.80/1.96  fof(f644,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl9_17 | spl9_29)),
% 12.80/1.96    inference(forward_demodulation,[],[f643,f184])).
% 12.80/1.96  fof(f643,plain,(
% 12.80/1.96    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl9_17 | spl9_29)),
% 12.80/1.96    inference(forward_demodulation,[],[f631,f391])).
% 12.80/1.96  fof(f695,plain,(
% 12.80/1.96    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl9_17),
% 12.80/1.96    inference(forward_demodulation,[],[f659,f184])).
% 12.80/1.96  fof(f659,plain,(
% 12.80/1.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl9_17),
% 12.80/1.96    inference(superposition,[],[f101,f391])).
% 12.80/1.96  fof(f652,plain,(
% 12.80/1.96    ~spl9_17 | spl9_26),
% 12.80/1.96    inference(avatar_contradiction_clause,[],[f651])).
% 12.80/1.96  fof(f651,plain,(
% 12.80/1.96    $false | (~spl9_17 | spl9_26)),
% 12.80/1.96    inference(subsumption_resolution,[],[f650,f244])).
% 12.80/1.96  fof(f650,plain,(
% 12.80/1.96    ~r1_tarski(k1_xboole_0,sK2) | (~spl9_17 | spl9_26)),
% 12.80/1.96    inference(forward_demodulation,[],[f649,f184])).
% 12.80/1.96  fof(f649,plain,(
% 12.80/1.96    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0),sK2) | (~spl9_17 | spl9_26)),
% 12.80/1.96    inference(forward_demodulation,[],[f615,f391])).
% 12.80/1.96  fof(f615,plain,(
% 12.80/1.96    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2) | spl9_26),
% 12.80/1.96    inference(avatar_component_clause,[],[f613])).
% 12.80/1.96  fof(f613,plain,(
% 12.80/1.96    spl9_26 <=> r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)),
% 12.80/1.96    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 12.80/1.96  fof(f642,plain,(
% 12.80/1.96    spl9_17 | spl9_31),
% 12.80/1.96    inference(avatar_split_clause,[],[f637,f639,f389])).
% 12.80/1.96  fof(f637,plain,(
% 12.80/1.96    u1_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK1)),
% 12.80/1.96    inference(forward_demodulation,[],[f413,f311])).
% 12.80/1.96  fof(f636,plain,(
% 12.80/1.96    ~spl9_28 | ~spl9_29 | spl9_30 | ~spl9_2),
% 12.80/1.96    inference(avatar_split_clause,[],[f623,f203,f633,f629,f625])).
% 12.80/1.96  fof(f623,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f542,f592])).
% 12.80/1.96  fof(f542,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f541,f267])).
% 12.80/1.96  fof(f541,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f540,f97])).
% 12.80/1.96  fof(f540,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f539,f98])).
% 12.80/1.96  fof(f539,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f538,f210])).
% 12.80/1.96  fof(f538,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f537,f209])).
% 12.80/1.96  fof(f537,plain,(
% 12.80/1.96    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl9_2),
% 12.80/1.96    inference(subsumption_resolution,[],[f533,f218])).
% 12.80/1.96  fof(f533,plain,(
% 12.80/1.96    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.80/1.96    inference(resolution,[],[f197,f208])).
% 12.80/1.96  fof(f620,plain,(
% 12.80/1.96    ~spl9_26 | spl9_27),
% 12.80/1.96    inference(avatar_split_clause,[],[f577,f617,f613])).
% 12.80/1.96  fof(f577,plain,(
% 12.80/1.96    k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = sK2 | ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)),
% 12.80/1.96    inference(resolution,[],[f242,f150])).
% 12.80/1.96  fof(f242,plain,(
% 12.80/1.96    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 12.80/1.96    inference(resolution,[],[f155,f101])).
% 12.80/1.96  fof(f392,plain,(
% 12.80/1.96    spl9_16 | spl9_17),
% 12.80/1.96    inference(avatar_split_clause,[],[f383,f389,f385])).
% 12.80/1.96  fof(f383,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0))),
% 12.80/1.96    inference(subsumption_resolution,[],[f382,f210])).
% 12.80/1.96  fof(f382,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 12.80/1.96    inference(subsumption_resolution,[],[f377,f100])).
% 12.80/1.96  fof(f377,plain,(
% 12.80/1.96    k1_xboole_0 = u1_struct_0(sK1) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 12.80/1.96    inference(resolution,[],[f192,f101])).
% 12.80/1.96  fof(f192,plain,(
% 12.80/1.96    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 12.80/1.96    inference(duplicate_literal_removal,[],[f170])).
% 12.80/1.96  fof(f170,plain,(
% 12.80/1.96    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 12.80/1.96    inference(cnf_transformation,[],[f59])).
% 12.80/1.96  fof(f59,plain,(
% 12.80/1.96    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 12.80/1.96    inference(flattening,[],[f58])).
% 12.80/1.96  fof(f58,plain,(
% 12.80/1.96    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 12.80/1.96    inference(ennf_transformation,[],[f21])).
% 12.80/1.96  fof(f21,axiom,(
% 12.80/1.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 12.80/1.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 12.80/1.96  fof(f339,plain,(
% 12.80/1.96    spl9_10 | ~spl9_11),
% 12.80/1.96    inference(avatar_split_clause,[],[f331,f336,f333])).
% 12.80/1.96  fof(f331,plain,(
% 12.80/1.96    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 12.80/1.96    inference(forward_demodulation,[],[f330,f313])).
% 12.80/1.96  fof(f330,plain,(
% 12.80/1.96    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 12.80/1.96    inference(resolution,[],[f215,f109])).
% 12.80/1.96  fof(f207,plain,(
% 12.80/1.96    spl9_1 | spl9_2),
% 12.80/1.96    inference(avatar_split_clause,[],[f106,f203,f199])).
% 12.80/1.96  fof(f106,plain,(
% 12.80/1.96    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 12.80/1.96    inference(cnf_transformation,[],[f70])).
% 12.80/1.96  fof(f206,plain,(
% 12.80/1.96    ~spl9_1 | ~spl9_2),
% 12.80/1.96    inference(avatar_split_clause,[],[f107,f203,f199])).
% 12.80/1.96  fof(f107,plain,(
% 12.80/1.96    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 12.80/1.96    inference(cnf_transformation,[],[f70])).
% 12.80/1.96  % SZS output end Proof for theBenchmark
% 12.80/1.96  % (16034)------------------------------
% 12.80/1.96  % (16034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.80/1.96  % (16034)Termination reason: Refutation
% 12.80/1.96  
% 12.80/1.96  % (16034)Memory used [KB]: 27888
% 12.80/1.96  % (16034)Time elapsed: 1.536 s
% 12.80/1.96  % (16034)------------------------------
% 12.80/1.96  % (16034)------------------------------
% 12.80/1.97  % (16023)Success in time 1.598 s
%------------------------------------------------------------------------------
