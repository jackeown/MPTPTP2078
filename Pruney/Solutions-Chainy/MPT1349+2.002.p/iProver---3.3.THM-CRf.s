%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:51 EST 2020

% Result     : Theorem 19.86s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :  431 (47644 expanded)
%              Number of clauses        :  340 (9868 expanded)
%              Number of leaves         :   22 (13912 expanded)
%              Depth                    :  120
%              Number of atoms          : 2339 (696922 expanded)
%              Number of equality atoms : 1199 (210809 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :   38 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                     => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                       => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
    inference(nnf_transformation,[],[f31])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
    inference(rectify,[],[f50])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK6))
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_funct_1(X2)
            | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
            | ~ v3_tops_2(X2,X0,X1) )
          & ( ( ! [X4] :
                  ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
            | v3_tops_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_funct_1(sK5)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) != k2_struct_0(X0)
          | ~ v3_tops_2(sK5,X0,X1) )
        & ( ( ! [X4] :
                ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & v2_funct_1(sK5)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) = k2_struct_0(X0) )
          | v3_tops_2(sK5,X0,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK4) )
            & ( ( ! [X4] :
                    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK4) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) != k2_struct_0(sK3)
                | ~ v3_tops_2(X2,sK3,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) = k2_struct_0(sK3) )
                | v3_tops_2(X2,sK3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) )
      | ~ v2_funct_1(sK5)
      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
      | ~ v3_tops_2(sK5,sK3,sK4) )
    & ( ( ! [X4] :
            ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
        & v2_funct_1(sK5)
        & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
        & k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) )
      | v3_tops_2(sK5,sK3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f51,f55,f54,f53,f52])).

fof(f92,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

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

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X4] :
      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_tops_2(sK5,sK3,sK4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,
    ( v2_funct_1(sK5)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,
    ( k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK5)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | ~ v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ? [X3] :
                      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2)))
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | ~ v2_funct_1(sK5)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | ~ v3_tops_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2621,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_643,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_39])).

cnf(c_644,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_648,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_38,c_37])).

cnf(c_649,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_2609,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0,X1,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_3338,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_2609])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3697,plain,
    ( m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3338,c_42,c_43,c_47,c_48])).

cnf(c_3698,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3697])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_30,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2625,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3436,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_2625])).

cnf(c_3764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3436,c_43])).

cnf(c_3765,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3764])).

cnf(c_3770,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_3765])).

cnf(c_4641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3770,c_43])).

cnf(c_4642,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_4647,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_4642])).

cnf(c_5528,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4647,c_43])).

cnf(c_5529,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5528])).

cnf(c_5534,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_5529])).

cnf(c_5639,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5534,c_43])).

cnf(c_5640,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5639])).

cnf(c_5645,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_5640])).

cnf(c_6386,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5645,c_43])).

cnf(c_6387,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6386])).

cnf(c_6392,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_6387])).

cnf(c_6495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6392,c_43])).

cnf(c_6496,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6495])).

cnf(c_6501,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_6496])).

cnf(c_7006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6501,c_43])).

cnf(c_7007,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7006])).

cnf(c_7012,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_7007])).

cnf(c_8560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7012,c_43])).

cnf(c_8561,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8560])).

cnf(c_8566,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_8561])).

cnf(c_9239,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8566,c_43])).

cnf(c_9240,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9239])).

cnf(c_9245,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_9240])).

cnf(c_10151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9245,c_43])).

cnf(c_10152,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10151])).

cnf(c_10157,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_10152])).

cnf(c_10907,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10157,c_43])).

cnf(c_10908,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10907])).

cnf(c_10913,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_10908])).

cnf(c_11546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10913,c_43])).

cnf(c_11547,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11546])).

cnf(c_11552,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_11547])).

cnf(c_12530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11552,c_43])).

cnf(c_12531,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12530])).

cnf(c_12536,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_12531])).

cnf(c_13408,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12536,c_43])).

cnf(c_13409,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13408])).

cnf(c_13414,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_13409])).

cnf(c_14454,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13414,c_43])).

cnf(c_14455,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14454])).

cnf(c_14460,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_14455])).

cnf(c_16094,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14460,c_43])).

cnf(c_16095,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16094])).

cnf(c_16100,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_16095])).

cnf(c_17124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16100,c_43])).

cnf(c_17125,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_17124])).

cnf(c_17130,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_17125])).

cnf(c_18145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17130,c_43])).

cnf(c_18146,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_18145])).

cnf(c_18151,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_18146])).

cnf(c_20243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18151,c_43])).

cnf(c_20244,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20243])).

cnf(c_20249,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_20244])).

cnf(c_21633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20249,c_43])).

cnf(c_21634,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21633])).

cnf(c_21639,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_21634])).

cnf(c_24870,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21639,c_43])).

cnf(c_24871,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24870])).

cnf(c_24876,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_24871])).

cnf(c_26281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24876,c_43])).

cnf(c_26282,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_26281])).

cnf(c_26287,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_26282])).

cnf(c_28365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26287,c_43])).

cnf(c_28366,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_28365])).

cnf(c_28371,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_28366])).

cnf(c_30021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28371,c_43])).

cnf(c_30022,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_30021])).

cnf(c_30027,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_30022])).

cnf(c_31215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30027,c_43])).

cnf(c_31216,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_31215])).

cnf(c_31221,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_31216])).

cnf(c_33531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31221,c_43])).

cnf(c_33532,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_33531])).

cnf(c_33537,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_33532])).

cnf(c_34962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33537,c_43])).

cnf(c_34963,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_34962])).

cnf(c_34968,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_34963])).

cnf(c_35701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34968,c_43])).

cnf(c_35702,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_35701])).

cnf(c_35707,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_35702])).

cnf(c_36875,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35707,c_43])).

cnf(c_36876,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_36875])).

cnf(c_36881,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_36876])).

cnf(c_37683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36881,c_43])).

cnf(c_37684,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37683])).

cnf(c_37689,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_37684])).

cnf(c_38490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37689,c_43])).

cnf(c_38491,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_38490])).

cnf(c_38496,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_38491])).

cnf(c_39485,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38496,c_43])).

cnf(c_39486,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_39485])).

cnf(c_39491,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_39486])).

cnf(c_40855,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39491,c_43])).

cnf(c_40856,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_40855])).

cnf(c_40861,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_40856])).

cnf(c_42129,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40861,c_43])).

cnf(c_42130,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_42129])).

cnf(c_42137,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3698,c_42130])).

cnf(c_45,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_46,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_127,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_129,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_2618,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2641,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3014,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2618,c_2641])).

cnf(c_31,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2624,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_52,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v2_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2702,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_tops_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2794,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | v2_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2702])).

cnf(c_2795,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_3019,plain,
    ( v2_funct_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2624,c_43,c_46,c_47,c_48,c_49,c_52,c_2795])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2964,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3061,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_3062,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3061])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2946,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3193,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(X0),u1_struct_0(sK3))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0,sK3)
    | m1_subset_1(sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_3654,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
    | m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_3655,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4126,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK4,X0)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4132,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK4,X0) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5))))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4126])).

cnf(c_4134,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4132])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4153,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4154,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4153])).

cnf(c_32,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2623,plain,
    ( k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2638,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v3_tops_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3991,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_2638])).

cnf(c_4073,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3991,c_43,c_46,c_47,c_48])).

cnf(c_4074,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_4073])).

cnf(c_4077,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2623,c_4074])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3006,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v3_tops_2(sK5,X0,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3008,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_1946,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3011,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) != X1
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | k2_struct_0(sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_3117,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_3118,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_3117])).

cnf(c_1945,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3585,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_4158,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4077,c_40,c_37,c_36,c_35,c_34,c_32,c_3008,c_3118,c_3585])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3640,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4201,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_3640])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4965,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5081,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
    | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5082,plain,
    ( v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5081])).

cnf(c_5084,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5082])).

cnf(c_2942,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6278,plain,
    ( ~ m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2942])).

cnf(c_6280,plain,
    ( m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6278])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2635,plain,
    ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3998,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_2635])).

cnf(c_33,negated_conjecture,
    ( v3_tops_2(sK5,sK3,sK4)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_50,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4082,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3998,c_43,c_46,c_47,c_48,c_50])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2640,plain,
    ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X2,X0,X1) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) != iProver_top
    | v3_tops_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4882,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4082,c_2640])).

cnf(c_4883,plain,
    ( k2_struct_0(sK4) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4882,c_4158])).

cnf(c_4884,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4883])).

cnf(c_6851,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4884,c_43,c_46,c_47,c_48,c_49,c_52,c_2795])).

cnf(c_6852,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_6851])).

cnf(c_8919,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_2633,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2634,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2630,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4387,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2630])).

cnf(c_9812,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4387,c_2625])).

cnf(c_10173,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9812,c_42,c_43])).

cnf(c_10174,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10173])).

cnf(c_10177,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_10174])).

cnf(c_10489,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10177,c_6852])).

cnf(c_11266,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10489,c_45,c_46,c_47,c_48,c_49,c_3062])).

cnf(c_11267,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_11266])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11341,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | ~ v2_funct_1(sK5)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK4)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_11342,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11341])).

cnf(c_10319,plain,
    ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_19025,plain,
    ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) ),
    inference(instantiation,[status(thm)],[c_10319])).

cnf(c_19030,plain,
    ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19025])).

cnf(c_1948,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_11207,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | X1 != sK4
    | k2_pre_topc(X1,X0) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_16638,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | k2_pre_topc(sK4,X0) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_11207])).

cnf(c_27052,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_16638])).

cnf(c_1947,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8417,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | X2 != X0
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X1 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_11833,plain,
    ( r1_tarski(X0,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | ~ r1_tarski(X1,k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | X0 != X1
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_8417])).

cnf(c_19024,plain,
    ( r1_tarski(X0,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | X0 != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_11833])).

cnf(c_30227,plain,
    ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_19024])).

cnf(c_30228,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30227])).

cnf(c_7776,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X2,sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X2,sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X1
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X0 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_8670,plain,
    ( ~ r1_tarski(k2_pre_topc(X0,X1),X2)
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X3,sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X3,sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X2
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(X0,X1) ),
    inference(instantiation,[status(thm)],[c_7776])).

cnf(c_33066,plain,
    ( ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
    inference(instantiation,[status(thm)],[c_8670])).

cnf(c_33067,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33066])).

cnf(c_33069,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33067])).

cnf(c_2628,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2) != k2_struct_0(X0)
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4162,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(sK5) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_2628])).

cnf(c_4230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4162,c_43,c_46,c_47,c_48,c_49,c_52,c_129,c_2795,c_3014])).

cnf(c_4231,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4230])).

cnf(c_9810,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4387,c_4231])).

cnf(c_39057,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9810,c_42,c_43])).

cnf(c_39058,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_39057])).

cnf(c_39061,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_39058])).

cnf(c_39360,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_39061,c_6852])).

cnf(c_2643,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3701,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3698,c_2625])).

cnf(c_11294,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3701,c_11267])).

cnf(c_11815,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_11294,c_4074])).

cnf(c_11949,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11815,c_3701,c_4074])).

cnf(c_39493,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3698,c_39486])).

cnf(c_39666,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39493,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,c_5084,c_6280,c_6852,c_8919,c_11267,c_11342,c_19030,c_27052,c_30228,c_33069,c_39360])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_577,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_578,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v3_tops_2(X0,X1,sK4)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_582,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ v3_tops_2(X0,X1,sK4)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_37])).

cnf(c_583,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v3_tops_2(X0,X1,sK4)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_2611,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X0,X1,sK4) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_2636,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4321,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2636])).

cnf(c_9141,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_4321])).

cnf(c_9898,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0)
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2611,c_9141])).

cnf(c_10265,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | v3_tops_2(X1,X0,sK4) != iProver_top
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9898,c_46])).

cnf(c_10266,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0)
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10265])).

cnf(c_10272,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_10266])).

cnf(c_10278,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10272,c_43,c_47,c_48,c_49,c_3062])).

cnf(c_10279,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_10278])).

cnf(c_39716,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_39666,c_10279])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_607,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_39])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_38,c_37])).

cnf(c_613,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | ~ v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_2610,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0,X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_39931,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))),k2_pre_topc(sK4,k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39716,c_2610])).

cnf(c_40146,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v5_pre_topc(sK5,sK3,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39931,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,c_5084,c_6280,c_6852,c_8919,c_10279,c_11267,c_11342,c_19030,c_27052,c_30228,c_33069,c_39360])).

cnf(c_40193,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_11949,c_40146])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_676,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_677,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_681,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_38,c_37])).

cnf(c_682,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
    | v5_pre_topc(X0,X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_2608,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(X0,X1,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0)))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_41841,plain,
    ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_40193,c_2608])).

cnf(c_2768,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
    | v5_pre_topc(sK5,X0,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,k2_pre_topc(X0,sK1(X0,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,sK1(X0,sK4,sK5))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_2769,plain,
    ( v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,X0,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,k2_pre_topc(X0,sK1(X0,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,sK1(X0,sK4,sK5)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2768])).

cnf(c_2771,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2769])).

cnf(c_8025,plain,
    ( v3_tops_2(sK5,sK3,sK4)
    | ~ m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_8028,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
    | v3_tops_2(sK5,sK3,sK4) = iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8025])).

cnf(c_3866,plain,
    ( X0 != X1
    | k2_pre_topc(X2,X3) != X1
    | k2_pre_topc(X2,X3) = X0 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_10688,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = X0
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_23121,plain,
    ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_10688])).

cnf(c_3878,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_pre_topc(X3,X4))
    | X2 != X0
    | k2_pre_topc(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_4591,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
    | r1_tarski(X3,k2_pre_topc(X1,X2))
    | X3 != X0
    | k2_pre_topc(X1,X2) != k2_pre_topc(X1,X2) ),
    inference(instantiation,[status(thm)],[c_3878])).

cnf(c_5693,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X2))
    | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X2))
    | X0 != k2_pre_topc(X1,X2)
    | k2_pre_topc(X1,X2) != k2_pre_topc(X1,X2) ),
    inference(instantiation,[status(thm)],[c_4591])).

cnf(c_33018,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))))
    | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))))
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_5693])).

cnf(c_33024,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33018])).

cnf(c_42333,plain,
    ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
    | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41841,c_42,c_43,c_47,c_48,c_49,c_2771,c_3698,c_4074,c_8028,c_11949,c_23121,c_33024])).

cnf(c_42334,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_42333])).

cnf(c_42337,plain,
    ( v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2643,c_42334])).

cnf(c_42340,plain,
    ( v3_tops_2(sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42137,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,c_5084,c_6280,c_6852,c_8919,c_11267,c_11342,c_19030,c_27052,c_30228,c_33069,c_39360,c_42337])).

cnf(c_29,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2626,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_56,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2883,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_43,c_46,c_47,c_48,c_49,c_52,c_56,c_2795])).

cnf(c_2884,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2883])).

cnf(c_4085,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | k2_struct_0(sK3) != k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4082,c_2884])).

cnf(c_4086,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4085])).

cnf(c_4167,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4086,c_40,c_37,c_36,c_35,c_34,c_32,c_3008,c_3118,c_3585])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_39])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_38,c_37])).

cnf(c_463,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_2614,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),X1,X2))
    | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(X1,sK4,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_3902,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),sK4,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2614])).

cnf(c_4561,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),sK4,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_3902])).

cnf(c_7485,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
    | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(X1,X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2611,c_4561])).

cnf(c_7573,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0))
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_7485])).

cnf(c_7581,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7573,c_42,c_43,c_47,c_48,c_49,c_3062])).

cnf(c_7588,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4167,c_7581])).

cnf(c_42402,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) ),
    inference(superposition,[status(thm)],[c_42340,c_7588])).

cnf(c_4236,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2642,c_4231])).

cnf(c_4970,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4236,c_43])).

cnf(c_4971,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4970])).

cnf(c_4977,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4167,c_4971])).

cnf(c_42411,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
    inference(superposition,[status(thm)],[c_42340,c_4977])).

cnf(c_4237,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4167,c_4231])).

cnf(c_42412,plain,
    ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) ),
    inference(superposition,[status(thm)],[c_42340,c_4237])).

cnf(c_42413,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_42402,c_42411,c_42412])).

cnf(c_28,negated_conjecture,
    ( ~ v3_tops_2(sK5,sK3,sK4)
    | ~ v2_funct_1(sK5)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2627,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_57,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3088,plain,
    ( v3_tops_2(sK5,sK3,sK4) != iProver_top
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2627,c_43,c_46,c_47,c_48,c_49,c_52,c_57,c_2795])).

cnf(c_3089,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
    | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
    | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3088])).

cnf(c_4084,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | k2_struct_0(sK3) != k2_struct_0(sK3)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4082,c_3089])).

cnf(c_4087,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
    | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4084])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42413,c_42340,c_4158,c_4087])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:43:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.86/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.86/2.99  
% 19.86/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.86/2.99  
% 19.86/2.99  ------  iProver source info
% 19.86/2.99  
% 19.86/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.86/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.86/2.99  git: non_committed_changes: false
% 19.86/2.99  git: last_make_outside_of_git: false
% 19.86/2.99  
% 19.86/2.99  ------ 
% 19.86/2.99  
% 19.86/2.99  ------ Input Options
% 19.86/2.99  
% 19.86/2.99  --out_options                           all
% 19.86/2.99  --tptp_safe_out                         true
% 19.86/2.99  --problem_path                          ""
% 19.86/2.99  --include_path                          ""
% 19.86/2.99  --clausifier                            res/vclausify_rel
% 19.86/2.99  --clausifier_options                    ""
% 19.86/2.99  --stdin                                 false
% 19.86/2.99  --stats_out                             all
% 19.86/2.99  
% 19.86/2.99  ------ General Options
% 19.86/2.99  
% 19.86/2.99  --fof                                   false
% 19.86/2.99  --time_out_real                         305.
% 19.86/2.99  --time_out_virtual                      -1.
% 19.86/2.99  --symbol_type_check                     false
% 19.86/2.99  --clausify_out                          false
% 19.86/2.99  --sig_cnt_out                           false
% 19.86/3.00  --trig_cnt_out                          false
% 19.86/3.00  --trig_cnt_out_tolerance                1.
% 19.86/3.00  --trig_cnt_out_sk_spl                   false
% 19.86/3.00  --abstr_cl_out                          false
% 19.86/3.00  
% 19.86/3.00  ------ Global Options
% 19.86/3.00  
% 19.86/3.00  --schedule                              default
% 19.86/3.00  --add_important_lit                     false
% 19.86/3.00  --prop_solver_per_cl                    1000
% 19.86/3.00  --min_unsat_core                        false
% 19.86/3.00  --soft_assumptions                      false
% 19.86/3.00  --soft_lemma_size                       3
% 19.86/3.00  --prop_impl_unit_size                   0
% 19.86/3.00  --prop_impl_unit                        []
% 19.86/3.00  --share_sel_clauses                     true
% 19.86/3.00  --reset_solvers                         false
% 19.86/3.00  --bc_imp_inh                            [conj_cone]
% 19.86/3.00  --conj_cone_tolerance                   3.
% 19.86/3.00  --extra_neg_conj                        none
% 19.86/3.00  --large_theory_mode                     true
% 19.86/3.00  --prolific_symb_bound                   200
% 19.86/3.00  --lt_threshold                          2000
% 19.86/3.00  --clause_weak_htbl                      true
% 19.86/3.00  --gc_record_bc_elim                     false
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing Options
% 19.86/3.00  
% 19.86/3.00  --preprocessing_flag                    true
% 19.86/3.00  --time_out_prep_mult                    0.1
% 19.86/3.00  --splitting_mode                        input
% 19.86/3.00  --splitting_grd                         true
% 19.86/3.00  --splitting_cvd                         false
% 19.86/3.00  --splitting_cvd_svl                     false
% 19.86/3.00  --splitting_nvd                         32
% 19.86/3.00  --sub_typing                            true
% 19.86/3.00  --prep_gs_sim                           true
% 19.86/3.00  --prep_unflatten                        true
% 19.86/3.00  --prep_res_sim                          true
% 19.86/3.00  --prep_upred                            true
% 19.86/3.00  --prep_sem_filter                       exhaustive
% 19.86/3.00  --prep_sem_filter_out                   false
% 19.86/3.00  --pred_elim                             true
% 19.86/3.00  --res_sim_input                         true
% 19.86/3.00  --eq_ax_congr_red                       true
% 19.86/3.00  --pure_diseq_elim                       true
% 19.86/3.00  --brand_transform                       false
% 19.86/3.00  --non_eq_to_eq                          false
% 19.86/3.00  --prep_def_merge                        true
% 19.86/3.00  --prep_def_merge_prop_impl              false
% 19.86/3.00  --prep_def_merge_mbd                    true
% 19.86/3.00  --prep_def_merge_tr_red                 false
% 19.86/3.00  --prep_def_merge_tr_cl                  false
% 19.86/3.00  --smt_preprocessing                     true
% 19.86/3.00  --smt_ac_axioms                         fast
% 19.86/3.00  --preprocessed_out                      false
% 19.86/3.00  --preprocessed_stats                    false
% 19.86/3.00  
% 19.86/3.00  ------ Abstraction refinement Options
% 19.86/3.00  
% 19.86/3.00  --abstr_ref                             []
% 19.86/3.00  --abstr_ref_prep                        false
% 19.86/3.00  --abstr_ref_until_sat                   false
% 19.86/3.00  --abstr_ref_sig_restrict                funpre
% 19.86/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/3.00  --abstr_ref_under                       []
% 19.86/3.00  
% 19.86/3.00  ------ SAT Options
% 19.86/3.00  
% 19.86/3.00  --sat_mode                              false
% 19.86/3.00  --sat_fm_restart_options                ""
% 19.86/3.00  --sat_gr_def                            false
% 19.86/3.00  --sat_epr_types                         true
% 19.86/3.00  --sat_non_cyclic_types                  false
% 19.86/3.00  --sat_finite_models                     false
% 19.86/3.00  --sat_fm_lemmas                         false
% 19.86/3.00  --sat_fm_prep                           false
% 19.86/3.00  --sat_fm_uc_incr                        true
% 19.86/3.00  --sat_out_model                         small
% 19.86/3.00  --sat_out_clauses                       false
% 19.86/3.00  
% 19.86/3.00  ------ QBF Options
% 19.86/3.00  
% 19.86/3.00  --qbf_mode                              false
% 19.86/3.00  --qbf_elim_univ                         false
% 19.86/3.00  --qbf_dom_inst                          none
% 19.86/3.00  --qbf_dom_pre_inst                      false
% 19.86/3.00  --qbf_sk_in                             false
% 19.86/3.00  --qbf_pred_elim                         true
% 19.86/3.00  --qbf_split                             512
% 19.86/3.00  
% 19.86/3.00  ------ BMC1 Options
% 19.86/3.00  
% 19.86/3.00  --bmc1_incremental                      false
% 19.86/3.00  --bmc1_axioms                           reachable_all
% 19.86/3.00  --bmc1_min_bound                        0
% 19.86/3.00  --bmc1_max_bound                        -1
% 19.86/3.00  --bmc1_max_bound_default                -1
% 19.86/3.00  --bmc1_symbol_reachability              true
% 19.86/3.00  --bmc1_property_lemmas                  false
% 19.86/3.00  --bmc1_k_induction                      false
% 19.86/3.00  --bmc1_non_equiv_states                 false
% 19.86/3.00  --bmc1_deadlock                         false
% 19.86/3.00  --bmc1_ucm                              false
% 19.86/3.00  --bmc1_add_unsat_core                   none
% 19.86/3.00  --bmc1_unsat_core_children              false
% 19.86/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/3.00  --bmc1_out_stat                         full
% 19.86/3.00  --bmc1_ground_init                      false
% 19.86/3.00  --bmc1_pre_inst_next_state              false
% 19.86/3.00  --bmc1_pre_inst_state                   false
% 19.86/3.00  --bmc1_pre_inst_reach_state             false
% 19.86/3.00  --bmc1_out_unsat_core                   false
% 19.86/3.00  --bmc1_aig_witness_out                  false
% 19.86/3.00  --bmc1_verbose                          false
% 19.86/3.00  --bmc1_dump_clauses_tptp                false
% 19.86/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.86/3.00  --bmc1_dump_file                        -
% 19.86/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.86/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.86/3.00  --bmc1_ucm_extend_mode                  1
% 19.86/3.00  --bmc1_ucm_init_mode                    2
% 19.86/3.00  --bmc1_ucm_cone_mode                    none
% 19.86/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.86/3.00  --bmc1_ucm_relax_model                  4
% 19.86/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.86/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/3.00  --bmc1_ucm_layered_model                none
% 19.86/3.00  --bmc1_ucm_max_lemma_size               10
% 19.86/3.00  
% 19.86/3.00  ------ AIG Options
% 19.86/3.00  
% 19.86/3.00  --aig_mode                              false
% 19.86/3.00  
% 19.86/3.00  ------ Instantiation Options
% 19.86/3.00  
% 19.86/3.00  --instantiation_flag                    true
% 19.86/3.00  --inst_sos_flag                         true
% 19.86/3.00  --inst_sos_phase                        true
% 19.86/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel_side                     num_symb
% 19.86/3.00  --inst_solver_per_active                1400
% 19.86/3.00  --inst_solver_calls_frac                1.
% 19.86/3.00  --inst_passive_queue_type               priority_queues
% 19.86/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/3.00  --inst_passive_queues_freq              [25;2]
% 19.86/3.00  --inst_dismatching                      true
% 19.86/3.00  --inst_eager_unprocessed_to_passive     true
% 19.86/3.00  --inst_prop_sim_given                   true
% 19.86/3.00  --inst_prop_sim_new                     false
% 19.86/3.00  --inst_subs_new                         false
% 19.86/3.00  --inst_eq_res_simp                      false
% 19.86/3.00  --inst_subs_given                       false
% 19.86/3.00  --inst_orphan_elimination               true
% 19.86/3.00  --inst_learning_loop_flag               true
% 19.86/3.00  --inst_learning_start                   3000
% 19.86/3.00  --inst_learning_factor                  2
% 19.86/3.00  --inst_start_prop_sim_after_learn       3
% 19.86/3.00  --inst_sel_renew                        solver
% 19.86/3.00  --inst_lit_activity_flag                true
% 19.86/3.00  --inst_restr_to_given                   false
% 19.86/3.00  --inst_activity_threshold               500
% 19.86/3.00  --inst_out_proof                        true
% 19.86/3.00  
% 19.86/3.00  ------ Resolution Options
% 19.86/3.00  
% 19.86/3.00  --resolution_flag                       true
% 19.86/3.00  --res_lit_sel                           adaptive
% 19.86/3.00  --res_lit_sel_side                      none
% 19.86/3.00  --res_ordering                          kbo
% 19.86/3.00  --res_to_prop_solver                    active
% 19.86/3.00  --res_prop_simpl_new                    false
% 19.86/3.00  --res_prop_simpl_given                  true
% 19.86/3.00  --res_passive_queue_type                priority_queues
% 19.86/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/3.00  --res_passive_queues_freq               [15;5]
% 19.86/3.00  --res_forward_subs                      full
% 19.86/3.00  --res_backward_subs                     full
% 19.86/3.00  --res_forward_subs_resolution           true
% 19.86/3.00  --res_backward_subs_resolution          true
% 19.86/3.00  --res_orphan_elimination                true
% 19.86/3.00  --res_time_limit                        2.
% 19.86/3.00  --res_out_proof                         true
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Options
% 19.86/3.00  
% 19.86/3.00  --superposition_flag                    true
% 19.86/3.00  --sup_passive_queue_type                priority_queues
% 19.86/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.86/3.00  --demod_completeness_check              fast
% 19.86/3.00  --demod_use_ground                      true
% 19.86/3.00  --sup_to_prop_solver                    passive
% 19.86/3.00  --sup_prop_simpl_new                    true
% 19.86/3.00  --sup_prop_simpl_given                  true
% 19.86/3.00  --sup_fun_splitting                     true
% 19.86/3.00  --sup_smt_interval                      50000
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Simplification Setup
% 19.86/3.00  
% 19.86/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.86/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.86/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.86/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.86/3.00  --sup_immed_triv                        [TrivRules]
% 19.86/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_immed_bw_main                     []
% 19.86/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.86/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_input_bw                          []
% 19.86/3.00  
% 19.86/3.00  ------ Combination Options
% 19.86/3.00  
% 19.86/3.00  --comb_res_mult                         3
% 19.86/3.00  --comb_sup_mult                         2
% 19.86/3.00  --comb_inst_mult                        10
% 19.86/3.00  
% 19.86/3.00  ------ Debug Options
% 19.86/3.00  
% 19.86/3.00  --dbg_backtrace                         false
% 19.86/3.00  --dbg_dump_prop_clauses                 false
% 19.86/3.00  --dbg_dump_prop_clauses_file            -
% 19.86/3.00  --dbg_out_stat                          false
% 19.86/3.00  ------ Parsing...
% 19.86/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.86/3.00  ------ Proving...
% 19.86/3.00  ------ Problem Properties 
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  clauses                                 37
% 19.86/3.00  conjectures                             13
% 19.86/3.00  EPR                                     9
% 19.86/3.00  Horn                                    30
% 19.86/3.00  unary                                   8
% 19.86/3.00  binary                                  4
% 19.86/3.00  lits                                    186
% 19.86/3.00  lits eq                                 21
% 19.86/3.00  fd_pure                                 0
% 19.86/3.00  fd_pseudo                               0
% 19.86/3.00  fd_cond                                 0
% 19.86/3.00  fd_pseudo_cond                          1
% 19.86/3.00  AC symbols                              0
% 19.86/3.00  
% 19.86/3.00  ------ Schedule dynamic 5 is on 
% 19.86/3.00  
% 19.86/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  ------ 
% 19.86/3.00  Current options:
% 19.86/3.00  ------ 
% 19.86/3.00  
% 19.86/3.00  ------ Input Options
% 19.86/3.00  
% 19.86/3.00  --out_options                           all
% 19.86/3.00  --tptp_safe_out                         true
% 19.86/3.00  --problem_path                          ""
% 19.86/3.00  --include_path                          ""
% 19.86/3.00  --clausifier                            res/vclausify_rel
% 19.86/3.00  --clausifier_options                    ""
% 19.86/3.00  --stdin                                 false
% 19.86/3.00  --stats_out                             all
% 19.86/3.00  
% 19.86/3.00  ------ General Options
% 19.86/3.00  
% 19.86/3.00  --fof                                   false
% 19.86/3.00  --time_out_real                         305.
% 19.86/3.00  --time_out_virtual                      -1.
% 19.86/3.00  --symbol_type_check                     false
% 19.86/3.00  --clausify_out                          false
% 19.86/3.00  --sig_cnt_out                           false
% 19.86/3.00  --trig_cnt_out                          false
% 19.86/3.00  --trig_cnt_out_tolerance                1.
% 19.86/3.00  --trig_cnt_out_sk_spl                   false
% 19.86/3.00  --abstr_cl_out                          false
% 19.86/3.00  
% 19.86/3.00  ------ Global Options
% 19.86/3.00  
% 19.86/3.00  --schedule                              default
% 19.86/3.00  --add_important_lit                     false
% 19.86/3.00  --prop_solver_per_cl                    1000
% 19.86/3.00  --min_unsat_core                        false
% 19.86/3.00  --soft_assumptions                      false
% 19.86/3.00  --soft_lemma_size                       3
% 19.86/3.00  --prop_impl_unit_size                   0
% 19.86/3.00  --prop_impl_unit                        []
% 19.86/3.00  --share_sel_clauses                     true
% 19.86/3.00  --reset_solvers                         false
% 19.86/3.00  --bc_imp_inh                            [conj_cone]
% 19.86/3.00  --conj_cone_tolerance                   3.
% 19.86/3.00  --extra_neg_conj                        none
% 19.86/3.00  --large_theory_mode                     true
% 19.86/3.00  --prolific_symb_bound                   200
% 19.86/3.00  --lt_threshold                          2000
% 19.86/3.00  --clause_weak_htbl                      true
% 19.86/3.00  --gc_record_bc_elim                     false
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing Options
% 19.86/3.00  
% 19.86/3.00  --preprocessing_flag                    true
% 19.86/3.00  --time_out_prep_mult                    0.1
% 19.86/3.00  --splitting_mode                        input
% 19.86/3.00  --splitting_grd                         true
% 19.86/3.00  --splitting_cvd                         false
% 19.86/3.00  --splitting_cvd_svl                     false
% 19.86/3.00  --splitting_nvd                         32
% 19.86/3.00  --sub_typing                            true
% 19.86/3.00  --prep_gs_sim                           true
% 19.86/3.00  --prep_unflatten                        true
% 19.86/3.00  --prep_res_sim                          true
% 19.86/3.00  --prep_upred                            true
% 19.86/3.00  --prep_sem_filter                       exhaustive
% 19.86/3.00  --prep_sem_filter_out                   false
% 19.86/3.00  --pred_elim                             true
% 19.86/3.00  --res_sim_input                         true
% 19.86/3.00  --eq_ax_congr_red                       true
% 19.86/3.00  --pure_diseq_elim                       true
% 19.86/3.00  --brand_transform                       false
% 19.86/3.00  --non_eq_to_eq                          false
% 19.86/3.00  --prep_def_merge                        true
% 19.86/3.00  --prep_def_merge_prop_impl              false
% 19.86/3.00  --prep_def_merge_mbd                    true
% 19.86/3.00  --prep_def_merge_tr_red                 false
% 19.86/3.00  --prep_def_merge_tr_cl                  false
% 19.86/3.00  --smt_preprocessing                     true
% 19.86/3.00  --smt_ac_axioms                         fast
% 19.86/3.00  --preprocessed_out                      false
% 19.86/3.00  --preprocessed_stats                    false
% 19.86/3.00  
% 19.86/3.00  ------ Abstraction refinement Options
% 19.86/3.00  
% 19.86/3.00  --abstr_ref                             []
% 19.86/3.00  --abstr_ref_prep                        false
% 19.86/3.00  --abstr_ref_until_sat                   false
% 19.86/3.00  --abstr_ref_sig_restrict                funpre
% 19.86/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.86/3.00  --abstr_ref_under                       []
% 19.86/3.00  
% 19.86/3.00  ------ SAT Options
% 19.86/3.00  
% 19.86/3.00  --sat_mode                              false
% 19.86/3.00  --sat_fm_restart_options                ""
% 19.86/3.00  --sat_gr_def                            false
% 19.86/3.00  --sat_epr_types                         true
% 19.86/3.00  --sat_non_cyclic_types                  false
% 19.86/3.00  --sat_finite_models                     false
% 19.86/3.00  --sat_fm_lemmas                         false
% 19.86/3.00  --sat_fm_prep                           false
% 19.86/3.00  --sat_fm_uc_incr                        true
% 19.86/3.00  --sat_out_model                         small
% 19.86/3.00  --sat_out_clauses                       false
% 19.86/3.00  
% 19.86/3.00  ------ QBF Options
% 19.86/3.00  
% 19.86/3.00  --qbf_mode                              false
% 19.86/3.00  --qbf_elim_univ                         false
% 19.86/3.00  --qbf_dom_inst                          none
% 19.86/3.00  --qbf_dom_pre_inst                      false
% 19.86/3.00  --qbf_sk_in                             false
% 19.86/3.00  --qbf_pred_elim                         true
% 19.86/3.00  --qbf_split                             512
% 19.86/3.00  
% 19.86/3.00  ------ BMC1 Options
% 19.86/3.00  
% 19.86/3.00  --bmc1_incremental                      false
% 19.86/3.00  --bmc1_axioms                           reachable_all
% 19.86/3.00  --bmc1_min_bound                        0
% 19.86/3.00  --bmc1_max_bound                        -1
% 19.86/3.00  --bmc1_max_bound_default                -1
% 19.86/3.00  --bmc1_symbol_reachability              true
% 19.86/3.00  --bmc1_property_lemmas                  false
% 19.86/3.00  --bmc1_k_induction                      false
% 19.86/3.00  --bmc1_non_equiv_states                 false
% 19.86/3.00  --bmc1_deadlock                         false
% 19.86/3.00  --bmc1_ucm                              false
% 19.86/3.00  --bmc1_add_unsat_core                   none
% 19.86/3.00  --bmc1_unsat_core_children              false
% 19.86/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.86/3.00  --bmc1_out_stat                         full
% 19.86/3.00  --bmc1_ground_init                      false
% 19.86/3.00  --bmc1_pre_inst_next_state              false
% 19.86/3.00  --bmc1_pre_inst_state                   false
% 19.86/3.00  --bmc1_pre_inst_reach_state             false
% 19.86/3.00  --bmc1_out_unsat_core                   false
% 19.86/3.00  --bmc1_aig_witness_out                  false
% 19.86/3.00  --bmc1_verbose                          false
% 19.86/3.00  --bmc1_dump_clauses_tptp                false
% 19.86/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.86/3.00  --bmc1_dump_file                        -
% 19.86/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.86/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.86/3.00  --bmc1_ucm_extend_mode                  1
% 19.86/3.00  --bmc1_ucm_init_mode                    2
% 19.86/3.00  --bmc1_ucm_cone_mode                    none
% 19.86/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.86/3.00  --bmc1_ucm_relax_model                  4
% 19.86/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.86/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.86/3.00  --bmc1_ucm_layered_model                none
% 19.86/3.00  --bmc1_ucm_max_lemma_size               10
% 19.86/3.00  
% 19.86/3.00  ------ AIG Options
% 19.86/3.00  
% 19.86/3.00  --aig_mode                              false
% 19.86/3.00  
% 19.86/3.00  ------ Instantiation Options
% 19.86/3.00  
% 19.86/3.00  --instantiation_flag                    true
% 19.86/3.00  --inst_sos_flag                         true
% 19.86/3.00  --inst_sos_phase                        true
% 19.86/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.86/3.00  --inst_lit_sel_side                     none
% 19.86/3.00  --inst_solver_per_active                1400
% 19.86/3.00  --inst_solver_calls_frac                1.
% 19.86/3.00  --inst_passive_queue_type               priority_queues
% 19.86/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.86/3.00  --inst_passive_queues_freq              [25;2]
% 19.86/3.00  --inst_dismatching                      true
% 19.86/3.00  --inst_eager_unprocessed_to_passive     true
% 19.86/3.00  --inst_prop_sim_given                   true
% 19.86/3.00  --inst_prop_sim_new                     false
% 19.86/3.00  --inst_subs_new                         false
% 19.86/3.00  --inst_eq_res_simp                      false
% 19.86/3.00  --inst_subs_given                       false
% 19.86/3.00  --inst_orphan_elimination               true
% 19.86/3.00  --inst_learning_loop_flag               true
% 19.86/3.00  --inst_learning_start                   3000
% 19.86/3.00  --inst_learning_factor                  2
% 19.86/3.00  --inst_start_prop_sim_after_learn       3
% 19.86/3.00  --inst_sel_renew                        solver
% 19.86/3.00  --inst_lit_activity_flag                true
% 19.86/3.00  --inst_restr_to_given                   false
% 19.86/3.00  --inst_activity_threshold               500
% 19.86/3.00  --inst_out_proof                        true
% 19.86/3.00  
% 19.86/3.00  ------ Resolution Options
% 19.86/3.00  
% 19.86/3.00  --resolution_flag                       false
% 19.86/3.00  --res_lit_sel                           adaptive
% 19.86/3.00  --res_lit_sel_side                      none
% 19.86/3.00  --res_ordering                          kbo
% 19.86/3.00  --res_to_prop_solver                    active
% 19.86/3.00  --res_prop_simpl_new                    false
% 19.86/3.00  --res_prop_simpl_given                  true
% 19.86/3.00  --res_passive_queue_type                priority_queues
% 19.86/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.86/3.00  --res_passive_queues_freq               [15;5]
% 19.86/3.00  --res_forward_subs                      full
% 19.86/3.00  --res_backward_subs                     full
% 19.86/3.00  --res_forward_subs_resolution           true
% 19.86/3.00  --res_backward_subs_resolution          true
% 19.86/3.00  --res_orphan_elimination                true
% 19.86/3.00  --res_time_limit                        2.
% 19.86/3.00  --res_out_proof                         true
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Options
% 19.86/3.00  
% 19.86/3.00  --superposition_flag                    true
% 19.86/3.00  --sup_passive_queue_type                priority_queues
% 19.86/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.86/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.86/3.00  --demod_completeness_check              fast
% 19.86/3.00  --demod_use_ground                      true
% 19.86/3.00  --sup_to_prop_solver                    passive
% 19.86/3.00  --sup_prop_simpl_new                    true
% 19.86/3.00  --sup_prop_simpl_given                  true
% 19.86/3.00  --sup_fun_splitting                     true
% 19.86/3.00  --sup_smt_interval                      50000
% 19.86/3.00  
% 19.86/3.00  ------ Superposition Simplification Setup
% 19.86/3.00  
% 19.86/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.86/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.86/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.86/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.86/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.86/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.86/3.00  --sup_immed_triv                        [TrivRules]
% 19.86/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_immed_bw_main                     []
% 19.86/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.86/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.86/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.86/3.00  --sup_input_bw                          []
% 19.86/3.00  
% 19.86/3.00  ------ Combination Options
% 19.86/3.00  
% 19.86/3.00  --comb_res_mult                         3
% 19.86/3.00  --comb_sup_mult                         2
% 19.86/3.00  --comb_inst_mult                        10
% 19.86/3.00  
% 19.86/3.00  ------ Debug Options
% 19.86/3.00  
% 19.86/3.00  --dbg_backtrace                         false
% 19.86/3.00  --dbg_dump_prop_clauses                 false
% 19.86/3.00  --dbg_dump_prop_clauses_file            -
% 19.86/3.00  --dbg_out_stat                          false
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  ------ Proving...
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  % SZS status Theorem for theBenchmark.p
% 19.86/3.00  
% 19.86/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.86/3.00  
% 19.86/3.00  fof(f11,conjecture,(
% 19.86/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f12,negated_conjecture,(
% 19.86/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 19.86/3.00    inference(negated_conjecture,[],[f11])).
% 19.86/3.00  
% 19.86/3.00  fof(f30,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 19.86/3.00    inference(ennf_transformation,[],[f12])).
% 19.86/3.00  
% 19.86/3.00  fof(f31,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f30])).
% 19.86/3.00  
% 19.86/3.00  fof(f49,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.86/3.00    inference(nnf_transformation,[],[f31])).
% 19.86/3.00  
% 19.86/3.00  fof(f50,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f49])).
% 19.86/3.00  
% 19.86/3.00  fof(f51,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 19.86/3.00    inference(rectify,[],[f50])).
% 19.86/3.00  
% 19.86/3.00  fof(f55,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f54,plain,(
% 19.86/3.00    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(sK5) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) != k2_struct_0(X0) | ~v3_tops_2(sK5,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(sK5) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5) = k2_struct_0(X0)) | v3_tops_2(sK5,X0,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f53,plain,(
% 19.86/3.00    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,sK4)) & ((! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,sK4)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f52,plain,(
% 19.86/3.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) != k2_struct_0(sK3) | ~v3_tops_2(X2,sK3,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2) = k2_struct_0(sK3)) | v3_tops_2(X2,sK3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f56,plain,(
% 19.86/3.00    ((((k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)) & ((! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & v2_funct_1(sK5) & k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) & k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)) | v3_tops_2(sK5,sK3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 19.86/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f51,f55,f54,f53,f52])).
% 19.86/3.00  
% 19.86/3.00  fof(f92,plain,(
% 19.86/3.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f7,axiom,(
% 19.86/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f22,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.86/3.00    inference(ennf_transformation,[],[f7])).
% 19.86/3.00  
% 19.86/3.00  fof(f23,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f22])).
% 19.86/3.00  
% 19.86/3.00  fof(f40,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(nnf_transformation,[],[f23])).
% 19.86/3.00  
% 19.86/3.00  fof(f41,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(rectify,[],[f40])).
% 19.86/3.00  
% 19.86/3.00  fof(f42,plain,(
% 19.86/3.00    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f43,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 19.86/3.00  
% 19.86/3.00  fof(f75,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f43])).
% 19.86/3.00  
% 19.86/3.00  fof(f87,plain,(
% 19.86/3.00    ~v2_struct_0(sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f88,plain,(
% 19.86/3.00    v2_pre_topc(sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f89,plain,(
% 19.86/3.00    l1_pre_topc(sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f85,plain,(
% 19.86/3.00    v2_pre_topc(sK3)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f86,plain,(
% 19.86/3.00    l1_pre_topc(sK3)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f90,plain,(
% 19.86/3.00    v1_funct_1(sK5)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f91,plain,(
% 19.86/3.00    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f2,axiom,(
% 19.86/3.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f13,plain,(
% 19.86/3.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.86/3.00    inference(ennf_transformation,[],[f2])).
% 19.86/3.00  
% 19.86/3.00  fof(f14,plain,(
% 19.86/3.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f13])).
% 19.86/3.00  
% 19.86/3.00  fof(f60,plain,(
% 19.86/3.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f14])).
% 19.86/3.00  
% 19.86/3.00  fof(f96,plain,(
% 19.86/3.00    ( ! [X4] : (k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X4)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) | v3_tops_2(sK5,sK3,sK4)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f3,axiom,(
% 19.86/3.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f15,plain,(
% 19.86/3.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(ennf_transformation,[],[f3])).
% 19.86/3.00  
% 19.86/3.00  fof(f61,plain,(
% 19.86/3.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f15])).
% 19.86/3.00  
% 19.86/3.00  fof(f95,plain,(
% 19.86/3.00    v2_funct_1(sK5) | v3_tops_2(sK5,sK3,sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f4,axiom,(
% 19.86/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f16,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(ennf_transformation,[],[f4])).
% 19.86/3.00  
% 19.86/3.00  fof(f17,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f16])).
% 19.86/3.00  
% 19.86/3.00  fof(f34,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(nnf_transformation,[],[f17])).
% 19.86/3.00  
% 19.86/3.00  fof(f35,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f34])).
% 19.86/3.00  
% 19.86/3.00  fof(f64,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f35])).
% 19.86/3.00  
% 19.86/3.00  fof(f5,axiom,(
% 19.86/3.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f18,plain,(
% 19.86/3.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.86/3.00    inference(ennf_transformation,[],[f5])).
% 19.86/3.00  
% 19.86/3.00  fof(f19,plain,(
% 19.86/3.00    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.86/3.00    inference(flattening,[],[f18])).
% 19.86/3.00  
% 19.86/3.00  fof(f68,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f19])).
% 19.86/3.00  
% 19.86/3.00  fof(f6,axiom,(
% 19.86/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f20,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.86/3.00    inference(ennf_transformation,[],[f6])).
% 19.86/3.00  
% 19.86/3.00  fof(f21,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f20])).
% 19.86/3.00  
% 19.86/3.00  fof(f36,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(nnf_transformation,[],[f21])).
% 19.86/3.00  
% 19.86/3.00  fof(f37,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(rectify,[],[f36])).
% 19.86/3.00  
% 19.86/3.00  fof(f38,plain,(
% 19.86/3.00    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f39,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.86/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 19.86/3.00  
% 19.86/3.00  fof(f72,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f39])).
% 19.86/3.00  
% 19.86/3.00  fof(f73,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f39])).
% 19.86/3.00  
% 19.86/3.00  fof(f69,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f19])).
% 19.86/3.00  
% 19.86/3.00  fof(f94,plain,(
% 19.86/3.00    k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | v3_tops_2(sK5,sK3,sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f65,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f35])).
% 19.86/3.00  
% 19.86/3.00  fof(f63,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f35])).
% 19.86/3.00  
% 19.86/3.00  fof(f1,axiom,(
% 19.86/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f32,plain,(
% 19.86/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.86/3.00    inference(nnf_transformation,[],[f1])).
% 19.86/3.00  
% 19.86/3.00  fof(f33,plain,(
% 19.86/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.86/3.00    inference(flattening,[],[f32])).
% 19.86/3.00  
% 19.86/3.00  fof(f59,plain,(
% 19.86/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f33])).
% 19.86/3.00  
% 19.86/3.00  fof(f58,plain,(
% 19.86/3.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.86/3.00    inference(cnf_transformation,[],[f33])).
% 19.86/3.00  
% 19.86/3.00  fof(f99,plain,(
% 19.86/3.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.86/3.00    inference(equality_resolution,[],[f58])).
% 19.86/3.00  
% 19.86/3.00  fof(f70,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f19])).
% 19.86/3.00  
% 19.86/3.00  fof(f62,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f35])).
% 19.86/3.00  
% 19.86/3.00  fof(f93,plain,(
% 19.86/3.00    k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) | v3_tops_2(sK5,sK3,sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f67,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f35])).
% 19.86/3.00  
% 19.86/3.00  fof(f8,axiom,(
% 19.86/3.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f24,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.86/3.00    inference(ennf_transformation,[],[f8])).
% 19.86/3.00  
% 19.86/3.00  fof(f25,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 19.86/3.00    inference(flattening,[],[f24])).
% 19.86/3.00  
% 19.86/3.00  fof(f77,plain,(
% 19.86/3.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f25])).
% 19.86/3.00  
% 19.86/3.00  fof(f9,axiom,(
% 19.86/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f26,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(ennf_transformation,[],[f9])).
% 19.86/3.00  
% 19.86/3.00  fof(f27,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 19.86/3.00    inference(flattening,[],[f26])).
% 19.86/3.00  
% 19.86/3.00  fof(f78,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f27])).
% 19.86/3.00  
% 19.86/3.00  fof(f74,plain,(
% 19.86/3.00    ( ! [X4,X2,X0,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f43])).
% 19.86/3.00  
% 19.86/3.00  fof(f76,plain,(
% 19.86/3.00    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f43])).
% 19.86/3.00  
% 19.86/3.00  fof(f97,plain,(
% 19.86/3.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  fof(f10,axiom,(
% 19.86/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 19.86/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.86/3.00  
% 19.86/3.00  fof(f28,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.86/3.00    inference(ennf_transformation,[],[f10])).
% 19.86/3.00  
% 19.86/3.00  fof(f29,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.86/3.00    inference(flattening,[],[f28])).
% 19.86/3.00  
% 19.86/3.00  fof(f44,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.86/3.00    inference(nnf_transformation,[],[f29])).
% 19.86/3.00  
% 19.86/3.00  fof(f45,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.86/3.00    inference(flattening,[],[f44])).
% 19.86/3.00  
% 19.86/3.00  fof(f46,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.86/3.00    inference(rectify,[],[f45])).
% 19.86/3.00  
% 19.86/3.00  fof(f47,plain,(
% 19.86/3.00    ! [X2,X1,X0] : (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 19.86/3.00    introduced(choice_axiom,[])).
% 19.86/3.00  
% 19.86/3.00  fof(f48,plain,(
% 19.86/3.00    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.86/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 19.86/3.00  
% 19.86/3.00  fof(f82,plain,(
% 19.86/3.00    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.86/3.00    inference(cnf_transformation,[],[f48])).
% 19.86/3.00  
% 19.86/3.00  fof(f98,plain,(
% 19.86/3.00    k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) | ~v2_funct_1(sK5) | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) | ~v3_tops_2(sK5,sK3,sK4)),
% 19.86/3.00    inference(cnf_transformation,[],[f56])).
% 19.86/3.00  
% 19.86/3.00  cnf(c_34,negated_conjecture,
% 19.86/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 19.86/3.00      inference(cnf_transformation,[],[f92]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2621,plain,
% 19.86/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_18,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | v2_struct_0(X2)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f75]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39,negated_conjecture,
% 19.86/3.00      ( ~ v2_struct_0(sK4) ),
% 19.86/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_643,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | sK4 != X2 ),
% 19.86/3.00      inference(resolution_lifted,[status(thm)],[c_18,c_39]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_644,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(unflattening,[status(thm)],[c_643]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_38,negated_conjecture,
% 19.86/3.00      ( v2_pre_topc(sK4) ),
% 19.86/3.00      inference(cnf_transformation,[],[f88]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_37,negated_conjecture,
% 19.86/3.00      ( l1_pre_topc(sK4) ),
% 19.86/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_648,plain,
% 19.86/3.00      ( ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_644,c_38,c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_649,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_648]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2609,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.86/3.00      | v2_pre_topc(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3338,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2621,c_2609]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_41,negated_conjecture,
% 19.86/3.00      ( v2_pre_topc(sK3) ),
% 19.86/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42,plain,
% 19.86/3.00      ( v2_pre_topc(sK3) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40,negated_conjecture,
% 19.86/3.00      ( l1_pre_topc(sK3) ),
% 19.86/3.00      inference(cnf_transformation,[],[f86]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_43,plain,
% 19.86/3.00      ( l1_pre_topc(sK3) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_36,negated_conjecture,
% 19.86/3.00      ( v1_funct_1(sK5) ),
% 19.86/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_47,plain,
% 19.86/3.00      ( v1_funct_1(sK5) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_35,negated_conjecture,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 19.86/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_48,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3697,plain,
% 19.86/3.00      ( m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_3338,c_42,c_43,c_47,c_48]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3698,plain,
% 19.86/3.00      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_3697]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3,plain,
% 19.86/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2642,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30,negated_conjecture,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
% 19.86/3.00      inference(cnf_transformation,[],[f96]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2625,plain,
% 19.86/3.00      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3436,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_2625]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3764,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_3436,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3765,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_3764]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3770,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_3765]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4641,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_3770,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4642,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_4641]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4647,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_4642]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5528,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4647,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5529,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_5528]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5534,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_5529]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5639,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_5534,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5640,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_5639]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5645,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_5640]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6386,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_5645,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6387,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_6386]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6392,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_6387]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6495,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_6392,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6496,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_6495]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6501,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_6496]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7006,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_6501,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7007,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_7006]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7012,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_7007]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8560,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_7012,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8561,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_8560]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8566,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_8561]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9239,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_8566,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9240,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_9239]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9245,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_9240]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10151,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_9245,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10152,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_10151]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10157,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_10152]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10907,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_10157,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10908,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_10907]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10913,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_10908]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11546,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_10913,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11547,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_11546]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11552,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_11547]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_12530,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_11552,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_12531,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_12530]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_12536,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_12531]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_13408,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_12536,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_13409,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_13408]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_13414,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_13409]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_14454,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_13414,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_14455,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_14454]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_14460,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_14455]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_16094,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_14460,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_16095,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_16094]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_16100,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_16095]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_17124,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_16100,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_17125,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_17124]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_17130,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_17125]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_18145,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_17130,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_18146,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_18145]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_18151,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_18146]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_20243,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_18151,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_20244,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_20243]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_20249,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_20244]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_21633,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_20249,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_21634,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_21633]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_21639,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_21634]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_24870,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_21639,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_24871,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_24870]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_24876,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_24871]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_26281,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_24876,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_26282,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_26281]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_26287,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_26282]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_28365,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_26287,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_28366,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_28365]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_28371,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_28366]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30021,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_28371,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30022,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_30021]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30027,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_30022]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_31215,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_30027,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_31216,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_31215]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_31221,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_31216]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33531,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_31221,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33532,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_33531]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33537,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_33532]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_34962,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_33537,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_34963,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_34962]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_34968,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_34963]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_35701,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_34968,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_35702,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_35701]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_35707,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_35702]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_36875,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_35707,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_36876,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_36875]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_36881,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_36876]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_37683,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_36881,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_37684,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_37683]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_37689,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_37684]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_38490,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_37689,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_38491,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_38490]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_38496,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_38491]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39485,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_38496,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39486,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_39485]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39491,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_39486]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40855,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_39491,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40856,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_40855]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40861,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_40856]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42129,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_40861,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42130,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0)))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,X0))))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_42129]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42137,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_3698,c_42130]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_45,plain,
% 19.86/3.00      ( v2_pre_topc(sK4) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_46,plain,
% 19.86/3.00      ( l1_pre_topc(sK4) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_49,plain,
% 19.86/3.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4,plain,
% 19.86/3.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 19.86/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_127,plain,
% 19.86/3.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_129,plain,
% 19.86/3.00      ( l1_struct_0(sK3) = iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_127]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2618,plain,
% 19.86/3.00      ( l1_pre_topc(sK4) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2641,plain,
% 19.86/3.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3014,plain,
% 19.86/3.00      ( l1_struct_0(sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2618,c_2641]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_31,negated_conjecture,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) | v2_funct_1(sK5) ),
% 19.86/3.00      inference(cnf_transformation,[],[f95]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2624,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v2_funct_1(sK5) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_52,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v2_funct_1(sK5) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | v2_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f64]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2702,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
% 19.86/3.00      | ~ v3_tops_2(sK5,X0,X1)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | v2_funct_1(sK5)
% 19.86/3.00      | ~ l1_pre_topc(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_8]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2794,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 19.86/3.00      | ~ v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | v2_funct_1(sK5)
% 19.86/3.00      | ~ l1_pre_topc(sK3)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_2702]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2795,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) = iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3019,plain,
% 19.86/3.00      ( v2_funct_1(sK5) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_2624,c_43,c_46,c_47,c_48,c_49,c_52,c_2795]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_13,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 19.86/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2964,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,X0,X1)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.86/3.00      | v1_funct_1(k2_tops_2(X0,X1,sK5))
% 19.86/3.00      | ~ v1_funct_1(sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3061,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
% 19.86/3.00      | ~ v1_funct_1(sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_2964]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3062,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_3061]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_15,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2946,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK3)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 19.86/3.00      | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(sK3)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK3) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_15]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3193,plain,
% 19.86/3.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(X0),u1_struct_0(sK3))
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0,sK3)
% 19.86/3.00      | m1_subset_1(sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 19.86/3.00      | ~ v2_pre_topc(X0)
% 19.86/3.00      | ~ v2_pre_topc(sK3)
% 19.86/3.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
% 19.86/3.00      | ~ l1_pre_topc(X0)
% 19.86/3.00      | ~ l1_pre_topc(sK3) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_2946]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3654,plain,
% 19.86/3.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3)
% 19.86/3.00      | m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 19.86/3.00      | ~ v2_pre_topc(sK3)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))
% 19.86/3.00      | ~ l1_pre_topc(sK3)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3193]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3655,plain,
% 19.86/3.00      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_3654]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_14,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4126,plain,
% 19.86/3.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(X0))
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK4,X0)
% 19.86/3.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | ~ v2_pre_topc(X0)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5))
% 19.86/3.00      | ~ l1_pre_topc(X0)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_14]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4132,plain,
% 19.86/3.00      ( v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK4,X0) = iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5))))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_4126]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4134,plain,
% 19.86/3.00      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_4132]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_12,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.86/3.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.86/3.00      | ~ v1_funct_1(X0) ),
% 19.86/3.00      inference(cnf_transformation,[],[f69]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4153,plain,
% 19.86/3.00      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3))
% 19.86/3.00      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_12]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4154,plain,
% 19.86/3.00      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_4153]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_32,negated_conjecture,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2623,plain,
% 19.86/3.00      ( k2_struct_0(sK4) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f65]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2638,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 19.86/3.00      | v3_tops_2(X0,X1,X2) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X2) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3991,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2621,c_2638]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4073,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_3991,c_43,c_46,c_47,c_48]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4074,plain,
% 19.86/3.00      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_4073]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4077,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2623,c_4074]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f63]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3006,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
% 19.86/3.00      | ~ v3_tops_2(sK5,X0,sK4)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | ~ l1_pre_topc(X0)
% 19.86/3.00      | ~ l1_pre_topc(sK4)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_9]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3008,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 19.86/3.00      | ~ v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | ~ l1_pre_topc(sK3)
% 19.86/3.00      | ~ l1_pre_topc(sK4)
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3006]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_1946,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3011,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) != X1
% 19.86/3.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 19.86/3.00      | k2_struct_0(sK4) != X1 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1946]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3117,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3011]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3118,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3117]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_1945,plain,( X0 = X0 ),theory(equality) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3585,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1945]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4158,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK4) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4077,c_40,c_37,c_36,c_35,c_34,c_32,c_3008,c_3118,
% 19.86/3.00                 c_3585]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_0,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.86/3.00      inference(cnf_transformation,[],[f59]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3640,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | X0 = sK4 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4201,plain,
% 19.86/3.00      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3640]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_1,plain,
% 19.86/3.00      ( r1_tarski(X0,X0) ),
% 19.86/3.00      inference(cnf_transformation,[],[f99]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4965,plain,
% 19.86/3.00      ( r1_tarski(sK4,sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.86/3.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 19.86/3.00      | ~ v1_funct_1(X0) ),
% 19.86/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5081,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_11]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5082,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_5081]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5084,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_5082]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2942,plain,
% 19.86/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ l1_pre_topc(sK3) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6278,plain,
% 19.86/3.00      ( ~ m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ l1_pre_topc(sK3) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_2942]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6280,plain,
% 19.86/3.00      ( m1_subset_1(sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_6278]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
% 19.86/3.00      inference(cnf_transformation,[],[f62]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2635,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.86/3.00      | v3_tops_2(X2,X0,X1) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3998,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2621,c_2635]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33,negated_conjecture,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 19.86/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_50,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4082,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) = k2_struct_0(sK3) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_3998,c_43,c_46,c_47,c_48,c_50]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 19.86/3.00      | v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v2_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2640,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X2,X0,X1) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) != iProver_top
% 19.86/3.00      | v3_tops_2(X2,X0,X1) = iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | v2_funct_1(X2) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4882,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4082,c_2640]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4883,plain,
% 19.86/3.00      ( k2_struct_0(sK4) != k2_struct_0(sK4)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(light_normalisation,[status(thm)],[c_4882,c_4158]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4884,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(equality_resolution_simp,[status(thm)],[c_4883]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6851,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4884,c_43,c_46,c_47,c_48,c_49,c_52,c_2795]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_6852,plain,
% 19.86/3.00      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK4,sK3) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_6851]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8919,plain,
% 19.86/3.00      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1945]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2633,plain,
% 19.86/3.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2634,plain,
% 19.86/3.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2630,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
% 19.86/3.00      | v2_pre_topc(X2) != iProver_top
% 19.86/3.00      | v2_pre_topc(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X2) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4387,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.86/3.00      | v2_pre_topc(X2) != iProver_top
% 19.86/3.00      | v2_pre_topc(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X2) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2634,c_2630]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9812,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4387,c_2625]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10173,plain,
% 19.86/3.00      ( l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_9812,c_42,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10174,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_10173]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10177,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2633,c_10174]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10489,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_10177,c_6852]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11266,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_10489,c_45,c_46,c_47,c_48,c_49,c_3062]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11267,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_11266]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_20,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v2_funct_1(X0)
% 19.86/3.00      | ~ l1_struct_0(X2)
% 19.86/3.00      | ~ l1_struct_0(X1)
% 19.86/3.00      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11341,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 19.86/3.00      | ~ m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | ~ v2_funct_1(sK5)
% 19.86/3.00      | ~ l1_struct_0(sK3)
% 19.86/3.00      | ~ l1_struct_0(sK4)
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_20]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11342,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_struct_0(sK3) != iProver_top
% 19.86/3.00      | l1_struct_0(sK4) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_11341]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10319,plain,
% 19.86/3.00      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X1)) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_19025,plain,
% 19.86/3.00      ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_10319]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_19030,plain,
% 19.86/3.00      ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_19025]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_1948,plain,
% 19.86/3.00      ( X0 != X1 | X2 != X3 | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
% 19.86/3.00      theory(equality) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11207,plain,
% 19.86/3.00      ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 19.86/3.00      | X1 != sK4
% 19.86/3.00      | k2_pre_topc(X1,X0) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1948]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_16638,plain,
% 19.86/3.00      ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,X0) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | sK4 != sK4 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_11207]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_27052,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | sK4 != sK4 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_16638]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_1947,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.86/3.00      theory(equality) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8417,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,X1)
% 19.86/3.00      | r1_tarski(X2,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | X2 != X0
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X1 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1947]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11833,plain,
% 19.86/3.00      ( r1_tarski(X0,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | ~ r1_tarski(X1,k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | X0 != X1
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_8417]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_19024,plain,
% 19.86/3.00      ( r1_tarski(X0,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | X0 != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_11833]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30227,plain,
% 19.86/3.00      ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_19024]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_30228,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_30227]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7776,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,X1)
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X2,sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X2,sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X1
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X2),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X2,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X0 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1947]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8670,plain,
% 19.86/3.00      ( ~ r1_tarski(k2_pre_topc(X0,X1),X2)
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X3,sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X3,sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != X2
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(X0,X1) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_7776]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33066,plain,
% 19.86/3.00      ( ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))))
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_8670]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33067,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(X0,sK0(sK4,X0,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_33066]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33069,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) != iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))),k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))) = iProver_top ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_33067]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2628,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2,X3)
% 19.86/3.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2) != k2_struct_0(X0)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | v2_funct_1(X2) != iProver_top
% 19.86/3.00      | l1_struct_0(X0) != iProver_top
% 19.86/3.00      | l1_struct_0(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4162,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_struct_0(sK3) != iProver_top
% 19.86/3.00      | l1_struct_0(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4158,c_2628]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4230,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4162,c_43,c_46,c_47,c_48,c_49,c_52,c_129,c_2795,
% 19.86/3.00                 c_3014]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4231,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0)
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_4230]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9810,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4387,c_4231]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39057,plain,
% 19.86/3.00      ( l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_9810,c_42,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39058,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_39057]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39061,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(X0,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1),X0,sK3) = iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2633,c_39058]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39360,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_39061,c_6852]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2643,plain,
% 19.86/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3701,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_3698,c_2625]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11294,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_3701,c_11267]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11815,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK0(sK4,sK3,k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5))))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_11294,c_4074]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_11949,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_11815,c_3701,c_4074]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39493,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_3698,c_39486]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39666,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_39493,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,
% 19.86/3.00                 c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,
% 19.86/3.00                 c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,
% 19.86/3.00                 c_5084,c_6280,c_6852,c_8919,c_11267,c_11342,c_19030,
% 19.86/3.00                 c_27052,c_30228,c_33069,c_39360]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_21,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | v2_struct_0(X2)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f78]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_577,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | sK4 != X2 ),
% 19.86/3.00      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_578,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,sK4)
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(unflattening,[status(thm)],[c_577]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_582,plain,
% 19.86/3.00      ( ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 19.86/3.00      | ~ v3_tops_2(X0,X1,sK4)
% 19.86/3.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_578,c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_583,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,sK4)
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_582]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2611,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(X0,X1,sK4) != iProver_top
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK4),X0),sK4,X1) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2636,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.86/3.00      | v3_tops_2(X2,X0,X1) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4321,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X1)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2634,c_2636]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9141,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X1)
% 19.86/3.00      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X2) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2633,c_4321]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_9898,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0)
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(X1,X0,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2611,c_9141]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10265,plain,
% 19.86/3.00      ( l1_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v3_tops_2(X1,X0,sK4) != iProver_top
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_9898,c_46]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10266,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) = k2_struct_0(X0)
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(X1,X0,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_10265]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10272,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2621,c_10266]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10278,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_10272,c_43,c_47,c_48,c_49,c_3062]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10279,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_10278]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39716,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_39666,c_10279]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_19,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 19.86/3.00      | v2_struct_0(X2)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f74]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_607,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | sK4 != X2 ),
% 19.86/3.00      inference(resolution_lifted,[status(thm)],[c_19,c_39]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_608,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(unflattening,[status(thm)],[c_607]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_612,plain,
% 19.86/3.00      ( ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 19.86/3.00      | ~ v2_pre_topc(X1) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_608,c_38,c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_613,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | ~ v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_612]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2610,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,X2))) = iProver_top
% 19.86/3.00      | v2_pre_topc(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_39931,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))))))))))))))))))))))))))))))))))),k2_pre_topc(sK4,k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))))))))))))))))))))))))))))))))))))) = iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_39716,c_2610]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40146,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_39931,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,
% 19.86/3.00                 c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,
% 19.86/3.00                 c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,
% 19.86/3.00                 c_5084,c_6280,c_6852,c_8919,c_10279,c_11267,c_11342,
% 19.86/3.00                 c_19030,c_27052,c_30228,c_33069,c_39360]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_40193,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3) ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_11949,c_40146]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_17,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 19.86/3.00      | v2_struct_0(X2)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2) ),
% 19.86/3.00      inference(cnf_transformation,[],[f76]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_676,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | v5_pre_topc(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | sK4 != X2 ),
% 19.86/3.00      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_677,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK4) ),
% 19.86/3.00      inference(unflattening,[status(thm)],[c_676]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_681,plain,
% 19.86/3.00      ( ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 19.86/3.00      | ~ v2_pre_topc(X1) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_677,c_38,c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_682,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0))))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1) ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_681]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2608,plain,
% 19.86/3.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(X0,X1,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,k2_pre_topc(X1,sK1(X1,sK4,X0))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK4),X0,sK1(X1,sK4,X0)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(X0) != iProver_top
% 19.86/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_41841,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) = k2_struct_0(sK3)
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_40193,c_2608]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2768,plain,
% 19.86/3.00      ( ~ v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4))
% 19.86/3.00      | v5_pre_topc(sK5,X0,sK4)
% 19.86/3.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
% 19.86/3.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,k2_pre_topc(X0,sK1(X0,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,sK1(X0,sK4,sK5))))
% 19.86/3.00      | ~ v2_pre_topc(X0)
% 19.86/3.00      | ~ v1_funct_1(sK5)
% 19.86/3.00      | ~ l1_pre_topc(X0) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_682]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2769,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,X0,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,k2_pre_topc(X0,sK1(X0,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),sK5,sK1(X0,sK4,sK5)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_2768]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2771,plain,
% 19.86/3.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_2769]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8025,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | ~ m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_30]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_8028,plain,
% 19.86/3.00      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | m1_subset_1(sK1(sK3,sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_8025]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3866,plain,
% 19.86/3.00      ( X0 != X1 | k2_pre_topc(X2,X3) != X1 | k2_pre_topc(X2,X3) = X0 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1946]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_10688,plain,
% 19.86/3.00      ( X0 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = X0
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3866]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_23121,plain,
% 19.86/3.00      ( k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_10688]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3878,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,X1)
% 19.86/3.00      | r1_tarski(X2,k2_pre_topc(X3,X4))
% 19.86/3.00      | X2 != X0
% 19.86/3.00      | k2_pre_topc(X3,X4) != X1 ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_1947]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4591,plain,
% 19.86/3.00      ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
% 19.86/3.00      | r1_tarski(X3,k2_pre_topc(X1,X2))
% 19.86/3.00      | X3 != X0
% 19.86/3.00      | k2_pre_topc(X1,X2) != k2_pre_topc(X1,X2) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_3878]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_5693,plain,
% 19.86/3.00      ( r1_tarski(X0,k2_pre_topc(X1,X2))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X2))
% 19.86/3.00      | X0 != k2_pre_topc(X1,X2)
% 19.86/3.00      | k2_pre_topc(X1,X2) != k2_pre_topc(X1,X2) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_4591]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33018,plain,
% 19.86/3.00      ( r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))))
% 19.86/3.00      | ~ r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))))
% 19.86/3.00      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) ),
% 19.86/3.00      inference(instantiation,[status(thm)],[c_5693]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_33024,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))
% 19.86/3.00      | r1_tarski(k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) = iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_33018]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42333,plain,
% 19.86/3.00      ( r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top
% 19.86/3.00      | v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_41841,c_42,c_43,c_47,c_48,c_49,c_2771,c_3698,c_4074,
% 19.86/3.00                 c_8028,c_11949,c_23121,c_33024]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42334,plain,
% 19.86/3.00      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top
% 19.86/3.00      | r1_tarski(k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5))),k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK1(sK3,sK4,sK5)))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_42333]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42337,plain,
% 19.86/3.00      ( v5_pre_topc(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2643,c_42334]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42340,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_42137,c_42,c_40,c_43,c_45,c_37,c_46,c_36,c_47,c_35,
% 19.86/3.00                 c_48,c_34,c_49,c_32,c_52,c_129,c_2795,c_3008,c_3014,
% 19.86/3.00                 c_3062,c_3118,c_3585,c_3655,c_4134,c_4154,c_4201,c_4965,
% 19.86/3.00                 c_5084,c_6280,c_6852,c_8919,c_11267,c_11342,c_19030,
% 19.86/3.00                 c_27052,c_30228,c_33069,c_39360,c_42337]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_29,negated_conjecture,
% 19.86/3.00      ( ~ v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
% 19.86/3.00      | ~ v2_funct_1(sK5)
% 19.86/3.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(cnf_transformation,[],[f97]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2626,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_56,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2883,plain,
% 19.86/3.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_2626,c_43,c_46,c_47,c_48,c_49,c_52,c_56,c_2795]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2884,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_2883]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4085,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | k2_struct_0(sK3) != k2_struct_0(sK3)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.86/3.00      inference(demodulation,[status(thm)],[c_4082,c_2884]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4086,plain,
% 19.86/3.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.86/3.00      inference(equality_resolution_simp,[status(thm)],[c_4085]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4167,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4086,c_40,c_37,c_36,c_35,c_34,c_32,c_3008,c_3118,
% 19.86/3.00                 c_3585]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_24,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 19.86/3.00      | v2_struct_0(X1)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) ),
% 19.86/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_457,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.86/3.00      | ~ v3_tops_2(X0,X1,X2)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.86/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(X2)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(X2)
% 19.86/3.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
% 19.86/3.00      | sK4 != X1 ),
% 19.86/3.00      inference(resolution_lifted,[status(thm)],[c_24,c_39]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_458,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 19.86/3.00      | ~ v3_tops_2(X0,sK4,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v2_pre_topc(sK4)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ l1_pre_topc(sK4)
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 19.86/3.00      inference(unflattening,[status(thm)],[c_457]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_462,plain,
% 19.86/3.00      ( ~ l1_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 19.86/3.00      | ~ v3_tops_2(X0,sK4,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_458,c_38,c_37]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_463,plain,
% 19.86/3.00      ( ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(X1))
% 19.86/3.00      | ~ v3_tops_2(X0,sK4,X1)
% 19.86/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 19.86/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.86/3.00      | ~ v2_pre_topc(X1)
% 19.86/3.00      | ~ v1_funct_1(X0)
% 19.86/3.00      | ~ l1_pre_topc(X1)
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X0,X2)) ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_462]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2614,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),X1,X2))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v3_tops_2(X1,sK4,X0) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3902,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v1_funct_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),u1_struct_0(sK4),u1_struct_0(X0)) != iProver_top
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),sK4,X0) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2634,c_2614]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4561,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),sK4,X0) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2633,c_3902]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7485,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),k2_pre_topc(X0,X2)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1),X2))
% 19.86/3.00      | v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(X1,X0,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) != iProver_top
% 19.86/3.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.86/3.00      | v2_pre_topc(X0) != iProver_top
% 19.86/3.00      | v1_funct_1(X1) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(sK4),X1)) != iProver_top
% 19.86/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2611,c_4561]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7573,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0))
% 19.86/3.00      | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | v2_pre_topc(sK3) != iProver_top
% 19.86/3.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5)) != iProver_top
% 19.86/3.00      | v1_funct_1(sK5) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2621,c_7485]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7581,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),X0))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_7573,c_42,c_43,c_47,c_48,c_49,c_3062]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_7588,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4167,c_7581]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42402,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6)) ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_42340,c_7588]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4236,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_2642,c_4231]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4970,plain,
% 19.86/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 19.86/3.00      | k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0)) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_4236,c_43]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4971,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,X0)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,X0))
% 19.86/3.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_4970]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4977,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4167,c_4971]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42411,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),k2_pre_topc(sK3,sK6)) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_42340,c_4977]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4237,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_4167,c_4231]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42412,plain,
% 19.86/3.00      ( k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK4),sK5),sK6) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6) ),
% 19.86/3.00      inference(superposition,[status(thm)],[c_42340,c_4237]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_42413,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) = k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) ),
% 19.86/3.00      inference(demodulation,[status(thm)],[c_42402,c_42411,c_42412]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_28,negated_conjecture,
% 19.86/3.00      ( ~ v3_tops_2(sK5,sK3,sK4)
% 19.86/3.00      | ~ v2_funct_1(sK5)
% 19.86/3.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) ),
% 19.86/3.00      inference(cnf_transformation,[],[f98]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_2627,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_57,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | v2_funct_1(sK5) != iProver_top ),
% 19.86/3.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3088,plain,
% 19.86/3.00      ( v3_tops_2(sK5,sK3,sK4) != iProver_top
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3) ),
% 19.86/3.00      inference(global_propositional_subsumption,
% 19.86/3.00                [status(thm)],
% 19.86/3.00                [c_2627,c_43,c_46,c_47,c_48,c_49,c_52,c_57,c_2795]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_3089,plain,
% 19.86/3.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK3)
% 19.86/3.00      | k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6)) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6))
% 19.86/3.00      | k2_struct_0(sK4) != k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(renaming,[status(thm)],[c_3088]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4084,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | k2_struct_0(sK3) != k2_struct_0(sK3)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(demodulation,[status(thm)],[c_4082,c_3089]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(c_4087,plain,
% 19.86/3.00      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_pre_topc(sK3,sK6)) != k2_pre_topc(sK4,k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,sK6))
% 19.86/3.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5) != k2_struct_0(sK4)
% 19.86/3.00      | v3_tops_2(sK5,sK3,sK4) != iProver_top ),
% 19.86/3.00      inference(equality_resolution_simp,[status(thm)],[c_4084]) ).
% 19.86/3.00  
% 19.86/3.00  cnf(contradiction,plain,
% 19.86/3.00      ( $false ),
% 19.86/3.00      inference(minisat,[status(thm)],[c_42413,c_42340,c_4158,c_4087]) ).
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.86/3.00  
% 19.86/3.00  ------                               Statistics
% 19.86/3.00  
% 19.86/3.00  ------ General
% 19.86/3.00  
% 19.86/3.00  abstr_ref_over_cycles:                  0
% 19.86/3.00  abstr_ref_under_cycles:                 0
% 19.86/3.00  gc_basic_clause_elim:                   0
% 19.86/3.00  forced_gc_time:                         0
% 19.86/3.00  parsing_time:                           0.011
% 19.86/3.00  unif_index_cands_time:                  0.
% 19.86/3.00  unif_index_add_time:                    0.
% 19.86/3.00  orderings_time:                         0.
% 19.86/3.00  out_proof_time:                         0.062
% 19.86/3.00  total_time:                             2.388
% 19.86/3.00  num_of_symbols:                         59
% 19.86/3.00  num_of_terms:                           28845
% 19.86/3.00  
% 19.86/3.00  ------ Preprocessing
% 19.86/3.00  
% 19.86/3.00  num_of_splits:                          0
% 19.86/3.00  num_of_split_atoms:                     0
% 19.86/3.00  num_of_reused_defs:                     0
% 19.86/3.00  num_eq_ax_congr_red:                    33
% 19.86/3.00  num_of_sem_filtered_clauses:            1
% 19.86/3.00  num_of_subtypes:                        0
% 19.86/3.00  monotx_restored_types:                  0
% 19.86/3.00  sat_num_of_epr_types:                   0
% 19.86/3.00  sat_num_of_non_cyclic_types:            0
% 19.86/3.00  sat_guarded_non_collapsed_types:        0
% 19.86/3.00  num_pure_diseq_elim:                    0
% 19.86/3.00  simp_replaced_by:                       0
% 19.86/3.00  res_preprocessed:                       196
% 19.86/3.00  prep_upred:                             0
% 19.86/3.00  prep_unflattend:                        19
% 19.86/3.00  smt_new_axioms:                         0
% 19.86/3.00  pred_elim_cands:                        10
% 19.86/3.00  pred_elim:                              1
% 19.86/3.00  pred_elim_cl:                           1
% 19.86/3.00  pred_elim_cycles:                       3
% 19.86/3.00  merged_defs:                            0
% 19.86/3.00  merged_defs_ncl:                        0
% 19.86/3.00  bin_hyper_res:                          0
% 19.86/3.00  prep_cycles:                            4
% 19.86/3.00  pred_elim_time:                         0.03
% 19.86/3.00  splitting_time:                         0.
% 19.86/3.00  sem_filter_time:                        0.
% 19.86/3.00  monotx_time:                            0.001
% 19.86/3.00  subtype_inf_time:                       0.
% 19.86/3.00  
% 19.86/3.00  ------ Problem properties
% 19.86/3.00  
% 19.86/3.00  clauses:                                37
% 19.86/3.00  conjectures:                            13
% 19.86/3.00  epr:                                    9
% 19.86/3.00  horn:                                   30
% 19.86/3.00  ground:                                 12
% 19.86/3.00  unary:                                  8
% 19.86/3.00  binary:                                 4
% 19.86/3.00  lits:                                   186
% 19.86/3.00  lits_eq:                                21
% 19.86/3.00  fd_pure:                                0
% 19.86/3.00  fd_pseudo:                              0
% 19.86/3.00  fd_cond:                                0
% 19.86/3.00  fd_pseudo_cond:                         1
% 19.86/3.00  ac_symbols:                             0
% 19.86/3.00  
% 19.86/3.00  ------ Propositional Solver
% 19.86/3.00  
% 19.86/3.00  prop_solver_calls:                      37
% 19.86/3.00  prop_fast_solver_calls:                 5863
% 19.86/3.00  smt_solver_calls:                       0
% 19.86/3.00  smt_fast_solver_calls:                  0
% 19.86/3.00  prop_num_of_clauses:                    14816
% 19.86/3.00  prop_preprocess_simplified:             27418
% 19.86/3.00  prop_fo_subsumed:                       499
% 19.86/3.00  prop_solver_time:                       0.
% 19.86/3.00  smt_solver_time:                        0.
% 19.86/3.00  smt_fast_solver_time:                   0.
% 19.86/3.00  prop_fast_solver_time:                  0.
% 19.86/3.00  prop_unsat_core_time:                   0.001
% 19.86/3.00  
% 19.86/3.00  ------ QBF
% 19.86/3.00  
% 19.86/3.00  qbf_q_res:                              0
% 19.86/3.00  qbf_num_tautologies:                    0
% 19.86/3.00  qbf_prep_cycles:                        0
% 19.86/3.00  
% 19.86/3.00  ------ BMC1
% 19.86/3.00  
% 19.86/3.00  bmc1_current_bound:                     -1
% 19.86/3.00  bmc1_last_solved_bound:                 -1
% 19.86/3.00  bmc1_unsat_core_size:                   -1
% 19.86/3.00  bmc1_unsat_core_parents_size:           -1
% 19.86/3.00  bmc1_merge_next_fun:                    0
% 19.86/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.86/3.00  
% 19.86/3.00  ------ Instantiation
% 19.86/3.00  
% 19.86/3.00  inst_num_of_clauses:                    3796
% 19.86/3.00  inst_num_in_passive:                    369
% 19.86/3.00  inst_num_in_active:                     2544
% 19.86/3.00  inst_num_in_unprocessed:                883
% 19.86/3.00  inst_num_of_loops:                      2910
% 19.86/3.00  inst_num_of_learning_restarts:          0
% 19.86/3.00  inst_num_moves_active_passive:          356
% 19.86/3.00  inst_lit_activity:                      0
% 19.86/3.00  inst_lit_activity_moves:                0
% 19.86/3.00  inst_num_tautologies:                   0
% 19.86/3.00  inst_num_prop_implied:                  0
% 19.86/3.00  inst_num_existing_simplified:           0
% 19.86/3.00  inst_num_eq_res_simplified:             0
% 19.86/3.00  inst_num_child_elim:                    0
% 19.86/3.00  inst_num_of_dismatching_blockings:      4022
% 19.86/3.00  inst_num_of_non_proper_insts:           9753
% 19.86/3.00  inst_num_of_duplicates:                 0
% 19.86/3.00  inst_inst_num_from_inst_to_res:         0
% 19.86/3.00  inst_dismatching_checking_time:         0.
% 19.86/3.00  
% 19.86/3.00  ------ Resolution
% 19.86/3.00  
% 19.86/3.00  res_num_of_clauses:                     0
% 19.86/3.00  res_num_in_passive:                     0
% 19.86/3.00  res_num_in_active:                      0
% 19.86/3.00  res_num_of_loops:                       200
% 19.86/3.00  res_forward_subset_subsumed:            896
% 19.86/3.00  res_backward_subset_subsumed:           2
% 19.86/3.00  res_forward_subsumed:                   0
% 19.86/3.00  res_backward_subsumed:                  0
% 19.86/3.00  res_forward_subsumption_resolution:     0
% 19.86/3.00  res_backward_subsumption_resolution:    0
% 19.86/3.00  res_clause_to_clause_subsumption:       13701
% 19.86/3.00  res_orphan_elimination:                 0
% 19.86/3.00  res_tautology_del:                      1313
% 19.86/3.00  res_num_eq_res_simplified:              0
% 19.86/3.00  res_num_sel_changes:                    0
% 19.86/3.00  res_moves_from_active_to_pass:          0
% 19.86/3.00  
% 19.86/3.00  ------ Superposition
% 19.86/3.00  
% 19.86/3.00  sup_time_total:                         0.
% 19.86/3.00  sup_time_generating:                    0.
% 19.86/3.00  sup_time_sim_full:                      0.
% 19.86/3.00  sup_time_sim_immed:                     0.
% 19.86/3.00  
% 19.86/3.00  sup_num_of_clauses:                     3181
% 19.86/3.00  sup_num_in_active:                      413
% 19.86/3.00  sup_num_in_passive:                     2768
% 19.86/3.00  sup_num_of_loops:                       581
% 19.86/3.00  sup_fw_superposition:                   1615
% 19.86/3.00  sup_bw_superposition:                   2165
% 19.86/3.00  sup_immediate_simplified:               331
% 19.86/3.00  sup_given_eliminated:                   0
% 19.86/3.00  comparisons_done:                       0
% 19.86/3.00  comparisons_avoided:                    729
% 19.86/3.00  
% 19.86/3.00  ------ Simplifications
% 19.86/3.00  
% 19.86/3.00  
% 19.86/3.00  sim_fw_subset_subsumed:                 178
% 19.86/3.00  sim_bw_subset_subsumed:                 35
% 19.86/3.00  sim_fw_subsumed:                        87
% 19.86/3.00  sim_bw_subsumed:                        139
% 19.86/3.00  sim_fw_subsumption_res:                 0
% 19.86/3.00  sim_bw_subsumption_res:                 0
% 19.86/3.00  sim_tautology_del:                      38
% 19.86/3.00  sim_eq_tautology_del:                   2
% 19.86/3.00  sim_eq_res_simp:                        3
% 19.86/3.00  sim_fw_demodulated:                     31
% 19.86/3.00  sim_bw_demodulated:                     34
% 19.86/3.00  sim_light_normalised:                   1
% 19.86/3.00  sim_joinable_taut:                      0
% 19.86/3.00  sim_joinable_simp:                      0
% 19.86/3.00  sim_ac_normalised:                      0
% 19.86/3.00  sim_smt_subsumption:                    0
% 19.86/3.00  
%------------------------------------------------------------------------------
