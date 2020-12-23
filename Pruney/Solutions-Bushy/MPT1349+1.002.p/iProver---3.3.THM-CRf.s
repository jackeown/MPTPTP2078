%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1349+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:32 EST 2020

% Result     : Theorem 15.68s
% Output     : CNFRefutation 15.68s
% Verified   : 
% Statistics : Number of formulae       :  326 (21498 expanded)
%              Number of clauses        :  236 (3544 expanded)
%              Number of leaves         :   22 (6611 expanded)
%              Depth                    :   31
%              Number of atoms          : 1861 (334382 expanded)
%              Number of equality atoms :  705 (98104 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   40 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
              ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_funct_1(sK4)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0)
          | ~ v3_tops_2(sK4,X0,X1) )
        & ( ( ! [X4] :
                ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & v2_funct_1(sK4)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) )
          | v3_tops_2(sK4,X0,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                  ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK3) )
            & ( ( ! [X4] :
                    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
                    ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X3))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2)
                | ~ v3_tops_2(X2,sK2,X1) )
              & ( ( ! [X4] :
                      ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2) )
                | v3_tops_2(X2,sK2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_funct_1(sK4)
      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
      | ~ v3_tops_2(sK4,sK2,sK3) )
    & ( ( ! [X4] :
            ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) )
        & v2_funct_1(sK4)
        & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
        & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) )
      | v3_tops_2(sK4,sK2,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f47,f51,f50,f49,f48])).

fof(f88,plain,
    ( v2_funct_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    ! [X4] :
      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_tops_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f90,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f61,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK1(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

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
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

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
    inference(cnf_transformation,[],[f40])).

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
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
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
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2311,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1080,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | v2_funct_1(sK4)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_1081,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_1080])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1083,plain,
    ( v2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1081,c_37,c_34,c_33,c_32,c_31])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1052,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_1053,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1052])).

cnf(c_1055,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_37,c_34,c_33,c_32,c_31])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1024,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_1025,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1024])).

cnf(c_1027,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_37,c_34,c_33,c_32,c_31])).

cnf(c_27,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_26,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_926,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_27,c_26])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1027,c_926])).

cnf(c_1063,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1055,c_1032])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1083,c_1063])).

cnf(c_2293,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_4228,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_2293])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11090,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4228,c_40])).

cnf(c_11091,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_11090])).

cnf(c_11099,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_11091])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_972,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_973,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_972])).

cnf(c_975,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_973,c_37,c_34,c_33,c_32,c_31])).

cnf(c_1034,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1027,c_975])).

cnf(c_1037,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_1082,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1138,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X3)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_1139,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_1138])).

cnf(c_1143,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1139,c_37,c_34,c_33,c_32,c_31])).

cnf(c_2288,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_4229,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_2288])).

cnf(c_6426,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4229,c_40])).

cnf(c_6427,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6426])).

cnf(c_6435,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_6427])).

cnf(c_2303,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_538,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_539,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_543,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_35,c_34])).

cnf(c_544,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_2295,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(X0,X1,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK1(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_3731,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2303,c_2295])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3780,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3731,c_39,c_40,c_44,c_45])).

cnf(c_3781,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3780])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2309,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4226,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1))) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_2309])).

cnf(c_8022,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))) = k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_4226])).

cnf(c_9805,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1))))) = k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1))))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_8022])).

cnf(c_12103,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))))) = k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,k2_pre_topc(X0,X1)))))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_9805])).

cnf(c_16225,plain,
    ( k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))))))) = k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3781,c_12103])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_571,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK1(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_572,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_576,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_35,c_34])).

cnf(c_577,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK1(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK1(X1,sK3,X0))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_2629,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | v5_pre_topc(sK4,X0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_2630,plain,
    ( v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,X0,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_2632,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1111,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X3)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X3))
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_1112,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_1111])).

cnf(c_1116,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1112,c_37,c_34,c_33,c_32,c_31])).

cnf(c_2289,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1116])).

cnf(c_3789,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3781,c_2289])).

cnf(c_1509,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5990,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_5995,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5990])).

cnf(c_1511,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5279,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK1(X2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK1(X2,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK1(X2,sK3,sK4))) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK1(X2,sK3,sK4))) != X1 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_5989,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,sK1(X1,sK3,sK4))))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,k2_pre_topc(X1,sK1(X1,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,sK1(X1,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,k2_pre_topc(X1,sK1(X1,sK3,sK4))) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,sK1(X1,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),sK4,sK1(X1,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5279])).

cnf(c_13286,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))))
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5989])).

cnf(c_13288,plain,
    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13286])).

cnf(c_13290,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))) = iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13288])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_13287,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_13292,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK1(X0,sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13287])).

cnf(c_13294,plain,
    ( r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK2,sK3,sK4)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13292])).

cnf(c_16362,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16225,c_39,c_40,c_44,c_45,c_46,c_2632,c_3789,c_5995,c_13290,c_13294])).

cnf(c_24396,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11099,c_39,c_37,c_40,c_34,c_43,c_33,c_44,c_32,c_45,c_31,c_46,c_1037,c_1053,c_1082,c_2632,c_3789,c_5995,c_13290,c_13294,c_21335])).

cnf(c_24397,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_24396])).

cnf(c_24405,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_24397])).

cnf(c_21334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6435,c_40])).

cnf(c_21335,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21334])).

cnf(c_21343,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_21335])).

cnf(c_32652,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24405,c_39,c_37,c_40,c_34,c_43,c_33,c_44,c_32,c_45,c_31,c_46,c_1037,c_1053,c_1082,c_2632,c_3789,c_5995,c_13290,c_13294,c_21343])).

cnf(c_32653,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_32652])).

cnf(c_32662,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),X1,X2)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),X1,X2))))))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_32653])).

cnf(c_42,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_14,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_85,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_87,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2680,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2753,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_2754,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2753])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2685,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2769,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_2770,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2769])).

cnf(c_2300,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2310,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2777,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_2310])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2690,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2785,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2690])).

cnf(c_2786,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2785])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2929,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
    | m1_subset_1(sK0(X0,X1,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3874,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_3875,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3874])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK0(X1,X2,X0))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2927,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,X1,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(X1,sK0(X0,X1,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3877,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_2927])).

cnf(c_3878,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3877])).

cnf(c_4360,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_5555,plain,
    ( ~ m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5556,plain,
    ( m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5555])).

cnf(c_2314,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2305,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5133,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2314,c_2305])).

cnf(c_2312,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2313,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15659,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X2,X1,k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5133,c_2312,c_2313])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1187,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1083])).

cnf(c_1188,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_1187])).

cnf(c_1192,plain,
    ( ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1188,c_33])).

cnf(c_1193,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X2) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X2)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_1192])).

cnf(c_2287,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),sK4),X2) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4,X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK4) != k2_struct_0(X0)
    | v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1193])).

cnf(c_2708,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_2287])).

cnf(c_3073,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2708,c_40,c_45,c_46,c_87,c_2777])).

cnf(c_3074,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3073])).

cnf(c_15676,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15659,c_3074])).

cnf(c_16401,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15676,c_39,c_40])).

cnf(c_16402,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_16401])).

cnf(c_1061,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1055,c_1034])).

cnf(c_1092,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1083,c_1061])).

cnf(c_2291,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_16413,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_16402,c_2291])).

cnf(c_15674,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15659,c_2288])).

cnf(c_16452,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15674,c_39,c_40])).

cnf(c_16453,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(X0,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1))))
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),X1),X0,sK2) = iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_16452])).

cnf(c_16468,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_16453])).

cnf(c_16470,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16468])).

cnf(c_19411,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_21177,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_19411])).

cnf(c_21179,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21177])).

cnf(c_1524,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_6660,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1)
    | X2 != sK3
    | k2_pre_topc(X2,X0) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1)) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_15645,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1)
    | k2_pre_topc(sK3,X0) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_6660])).

cnf(c_39378,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_15645])).

cnf(c_1510,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6173,plain,
    ( X0 != X1
    | X0 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_12261,plain,
    ( X0 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | X0 != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_6173])).

cnf(c_45523,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_12261])).

cnf(c_5605,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X1
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_21178,plain,
    ( ~ r1_tarski(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0 ),
    inference(instantiation,[status(thm)],[c_5605])).

cnf(c_46555,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_21178])).

cnf(c_46557,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46555])).

cnf(c_12070,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_46556,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) ),
    inference(instantiation,[status(thm)],[c_12070])).

cnf(c_46559,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46556])).

cnf(c_47015,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32662,c_39,c_37,c_40,c_42,c_34,c_43,c_33,c_44,c_32,c_45,c_31,c_46,c_87,c_1037,c_1053,c_1082,c_2632,c_2754,c_2770,c_2777,c_2786,c_3789,c_3875,c_3878,c_4360,c_5556,c_5995,c_13290,c_13294,c_16413,c_16470,c_21179,c_39378,c_45523,c_46557,c_46559])).

cnf(c_47047,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_47015,c_3074])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2304,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)),k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3))) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2317,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5119,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)),k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_2317])).

cnf(c_47130,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_47047,c_5119])).

cnf(c_2316,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2308,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4125,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),X1,X2))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k7_relset_1(X0,u1_struct_0(sK2),X1,X2)))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_2293])).

cnf(c_9545,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),X1,X2))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k7_relset_1(X0,u1_struct_0(sK2),X1,X2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(X1,k2_zfmisc_1(X0,u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_4125])).

cnf(c_19907,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),k2_zfmisc_1(X0,u1_struct_0(sK2)),X1))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k7_relset_1(X0,u1_struct_0(sK2),k2_zfmisc_1(X0,u1_struct_0(sK2)),X1)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_9545])).

cnf(c_4231,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_3074])).

cnf(c_4502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4231,c_40])).

cnf(c_4503,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4502])).

cnf(c_19932,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k7_relset_1(X0,u1_struct_0(sK2),k2_zfmisc_1(X0,u1_struct_0(sK2)),X1))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k7_relset_1(X0,u1_struct_0(sK2),k2_zfmisc_1(X0,u1_struct_0(sK2)),X1))) ),
    inference(superposition,[status(thm)],[c_19907,c_4503])).

cnf(c_22294,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | m1_subset_1(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k7_relset_1(X0,u1_struct_0(sK2),k2_zfmisc_1(X0,u1_struct_0(sK2)),X1))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19932,c_2311])).

cnf(c_3833,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3834,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3833])).

cnf(c_21159,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_19411])).

cnf(c_21162,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21159])).

cnf(c_46846,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22294,c_39,c_37,c_40,c_42,c_34,c_43,c_33,c_44,c_32,c_45,c_31,c_46,c_87,c_1037,c_1053,c_1082,c_2632,c_2754,c_2770,c_2777,c_2786,c_3789,c_3834,c_3875,c_3878,c_4360,c_5556,c_5995,c_13290,c_13294,c_16413,c_16470,c_21162,c_21179,c_39378,c_45523,c_46557,c_46559])).

cnf(c_47142,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_47130,c_46846,c_47047])).

cnf(c_47045,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_47015,c_2288])).

cnf(c_16364,plain,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16362])).

cnf(c_5582,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK2)
    | k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),sK4) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_12352,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5582])).

cnf(c_12353,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12352])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_502,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_36])).

cnf(c_503,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_507,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_35,c_34])).

cnf(c_508,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_2624,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_3827,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_3828,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3827])).

cnf(c_25,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_998,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | sK4 != X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_999,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_998])).

cnf(c_1001,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_999,c_37,c_34,c_33,c_32,c_31])).

cnf(c_1035,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1027,c_1001])).

cnf(c_1060,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1055,c_1035])).

cnf(c_1093,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1083,c_1060])).

cnf(c_1094,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1093])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47142,c_47045,c_47015,c_46556,c_46555,c_45523,c_39378,c_21179,c_16470,c_16364,c_16362,c_12353,c_5556,c_4360,c_3877,c_3875,c_3828,c_2786,c_2785,c_2777,c_2770,c_2769,c_2754,c_2753,c_1094,c_1081,c_1060,c_1053,c_87,c_46,c_31,c_45,c_32,c_44,c_33,c_43,c_34,c_42,c_35,c_40,c_37,c_39,c_38])).


%------------------------------------------------------------------------------
