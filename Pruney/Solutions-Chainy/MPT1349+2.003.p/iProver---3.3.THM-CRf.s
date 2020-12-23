%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:51 EST 2020

% Result     : Theorem 51.76s
% Output     : CNFRefutation 51.76s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3305)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f48])).

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
    inference(rectify,[],[f49])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).

fof(f93,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f55])).

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
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( v2_funct_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f43])).

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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ( k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f27])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f97,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f21])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))))
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))))
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,(
    ! [X4] :
      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_tops_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2)))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_566,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_107143,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != X1
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(X2,X1)
    | sK3 != X2 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_110113,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != X1
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_107143])).

cnf(c_142211,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_110113])).

cnf(c_32,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1238,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1236,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1258,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3784,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1258])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_46,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_48,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4095,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_43,c_46,c_47,c_48,c_49,c_2135])).

cnf(c_4096,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4095])).

cnf(c_4101,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_1238,c_4096])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1249,plain,
    ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2) != k2_struct_0(X0)
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4529,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_1249])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_127,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_129,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_1233,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1263,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1979,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_1263])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1259,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v3_tops_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2848,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1259])).

cnf(c_31,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_52,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3062,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2848,c_43,c_46,c_47,c_48,c_52])).

cnf(c_2285,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) = k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3303,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_3304,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3303])).

cnf(c_3306,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3304])).

cnf(c_5032,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4529,c_40,c_39,c_36,c_35,c_34,c_128,c_1985,c_3064,c_3305,c_4101])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1244,plain,
    ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5035,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5032,c_1244])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_45,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1853,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2069,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_2070,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1858,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2122,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_2123,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1863,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2125,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1863])).

cnf(c_2126,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2287,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4))
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3300,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_3301,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3300])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2286,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) = k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3308,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_3309,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(X0)
    | v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3308])).

cnf(c_3311,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_3032,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
    | m1_subset_1(sK1(X0,X1,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4742,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(X0))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,X0)
    | m1_subset_1(sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_4743,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,X0) = iProver_top
    | m1_subset_1(sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_4745,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4743])).

cnf(c_10731,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5035,c_42,c_40,c_43,c_39,c_44,c_45,c_46,c_36,c_47,c_35,c_48,c_34,c_49,c_52,c_128,c_129,c_1979,c_1985,c_2070,c_2123,c_2126,c_2848,c_3064,c_3301,c_3305,c_3310,c_4101,c_4745])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_1247,plain,
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

cnf(c_5235,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_1247])).

cnf(c_5603,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_43,c_46,c_47,c_48,c_49,c_52,c_129,c_1979,c_2848])).

cnf(c_5604,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5603])).

cnf(c_5611,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_5604])).

cnf(c_6006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5611,c_43])).

cnf(c_6007,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6006])).

cnf(c_10745,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_10731,c_6007])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2206,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2790,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2206])).

cnf(c_2791,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2790])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1257,plain,
    ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3645,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1257])).

cnf(c_33,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_50,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3957,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3645,c_43,c_46,c_47,c_48,c_50])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_1262,plain,
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

cnf(c_5557,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3957,c_1262])).

cnf(c_5589,plain,
    ( k2_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5557,c_4101])).

cnf(c_5590,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5589])).

cnf(c_6264,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5590,c_43,c_46,c_47,c_48,c_49,c_52,c_2848])).

cnf(c_6265,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6264])).

cnf(c_29,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1241,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3960,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_struct_0(sK2) != k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3957,c_1241])).

cnf(c_4082,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3960])).

cnf(c_564,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2586,plain,
    ( v3_tops_2(sK4,sK2,sK3)
    | X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = X0 ),
    inference(resolution,[status(thm)],[c_564,c_32])).

cnf(c_1822,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != X0
    | k2_struct_0(sK3) != X0
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_2054,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_563,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2055,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_1918,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_tops_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2134,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_2056,plain,
    ( X0 != X1
    | k2_struct_0(sK3) != X1
    | k2_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_2642,plain,
    ( X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = X0
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2918,plain,
    ( X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_40,c_37,c_36,c_35,c_34,c_2054,c_2055,c_2134,c_2642])).

cnf(c_2935,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(resolution,[status(thm)],[c_2918,c_563])).

cnf(c_3364,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2935,c_29])).

cnf(c_1923,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_tops_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2137,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_3064,plain,
    ( v2_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3062])).

cnf(c_3501,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3364,c_40,c_37,c_36,c_35,c_34,c_29,c_2137,c_2935,c_3064])).

cnf(c_3503,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3501])).

cnf(c_4084,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4082,c_3503])).

cnf(c_4085,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4084])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1246,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v3_tops_2(X0,X1,X2) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1256,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_1243,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2697,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1243])).

cnf(c_1254,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1255,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6287,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2697,c_1254,c_1255])).

cnf(c_6291,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v3_tops_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_6287])).

cnf(c_19254,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_6291])).

cnf(c_19900,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19254,c_42,c_43,c_44,c_45,c_46,c_47,c_48])).

cnf(c_19909,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_19900])).

cnf(c_20083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19909,c_43])).

cnf(c_20084,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20083])).

cnf(c_20092,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_20084])).

cnf(c_21093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20092,c_43])).

cnf(c_21094,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21093])).

cnf(c_21102,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_21094])).

cnf(c_21149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21102,c_43])).

cnf(c_21150,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21149])).

cnf(c_21158,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_21150])).

cnf(c_21379,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21158,c_43])).

cnf(c_21380,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21379])).

cnf(c_21388,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_21380])).

cnf(c_21435,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21388,c_43])).

cnf(c_21436,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21435])).

cnf(c_21444,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_21436])).

cnf(c_21654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21444,c_43])).

cnf(c_21655,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21654])).

cnf(c_21663,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_21655])).

cnf(c_22999,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21663,c_43])).

cnf(c_23000,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22999])).

cnf(c_23008,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_23000])).

cnf(c_25115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23008,c_43])).

cnf(c_25116,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_25115])).

cnf(c_25124,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_25116])).

cnf(c_27501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25124,c_43])).

cnf(c_27502,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27501])).

cnf(c_27511,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK5))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK5)))))))))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4085,c_27502])).

cnf(c_2078,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_2514,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_5612,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4085,c_5604])).

cnf(c_6015,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4085,c_6007])).

cnf(c_2519,plain,
    ( X0 != X1
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X1
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_4289,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = X0
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_6082,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_4289])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3925,plain,
    ( ~ r1_tarski(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),X0)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6124,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3925])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4585,plain,
    ( r1_tarski(k7_relset_1(X0,X1,X2,X3),k7_relset_1(X0,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6125,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_4585])).

cnf(c_28,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3365,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2935,c_28])).

cnf(c_1242,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_57,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1908,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_tops_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2128,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_2129,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2128])).

cnf(c_2135,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2134])).

cnf(c_2138,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_2153,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_43,c_46,c_47,c_48,c_49,c_57,c_2054,c_2055,c_2129,c_2135,c_2138])).

cnf(c_2154,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2153])).

cnf(c_2155,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2154])).

cnf(c_4378,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_2155])).

cnf(c_4394,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) ),
    inference(resolution,[status(thm)],[c_4378,c_0])).

cnf(c_1814,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1913,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | ~ v3_tops_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2131,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_2375,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v5_pre_topc(X0,sK2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,k2_pre_topc(sK2,sK5)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,sK5)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2950,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_7785,plain,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4394,c_41,c_40,c_43,c_39,c_38,c_37,c_46,c_36,c_47,c_35,c_48,c_34,c_50,c_29,c_1814,c_2131,c_2155,c_2935,c_2950,c_3064,c_3645])).

cnf(c_7787,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7785])).

cnf(c_3931,plain,
    ( X0 != X1
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X1
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_6257,plain,
    ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3931])).

cnf(c_9239,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_6257])).

cnf(c_2046,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(X1,X0)
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_2639,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_10049,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_565,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2019,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_6557,plain,
    ( ~ r1_tarski(X0,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)))
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_10334,plain,
    ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)))
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_6557])).

cnf(c_10336,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10334])).

cnf(c_10335,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_10338,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10335])).

cnf(c_30,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1240,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10750,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10731,c_1240])).

cnf(c_1933,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X1,X0)
    | ~ v3_tops_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2143,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_2144,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_10944,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10750,c_43,c_44,c_46,c_47,c_48,c_49,c_2144])).

cnf(c_10945,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_10944])).

cnf(c_10952,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10945,c_6287])).

cnf(c_11991,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10952,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49])).

cnf(c_11992,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11991])).

cnf(c_12001,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4085,c_11992])).

cnf(c_56,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2385,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ v3_tops_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK5)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2956,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK5)) ),
    inference(instantiation,[status(thm)],[c_2385])).

cnf(c_3562,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_2956])).

cnf(c_3563,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3562])).

cnf(c_17887,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12001,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_52,c_56,c_2070,c_2123,c_2126,c_2144,c_2848,c_2935,c_3563,c_3645])).

cnf(c_2044,plain,
    ( X0 != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X1
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_15945,plain,
    ( X0 != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_27629,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_15945])).

cnf(c_28255,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27511,c_2078,c_2514,c_5612,c_6015,c_6082,c_6124,c_6125,c_7787,c_9239,c_10049,c_10336,c_10338,c_17887,c_27629])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1252,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4472,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1252])).

cnf(c_4616,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4472,c_42,c_43,c_44,c_45,c_46,c_47,c_48])).

cnf(c_6014,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_6007])).

cnf(c_6477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6014,c_43])).

cnf(c_6478,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6477])).

cnf(c_6485,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_6478])).

cnf(c_6508,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6485,c_43])).

cnf(c_6509,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6508])).

cnf(c_6516,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_6509])).

cnf(c_6634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6516,c_43])).

cnf(c_6635,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6634])).

cnf(c_6642,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_6635])).

cnf(c_7553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6642,c_43])).

cnf(c_7554,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7553])).

cnf(c_7561,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_7554])).

cnf(c_8884,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7561,c_43])).

cnf(c_8885,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8884])).

cnf(c_8892,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_8885])).

cnf(c_10261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8892,c_43])).

cnf(c_10262,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10261])).

cnf(c_10269,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_10262])).

cnf(c_11628,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10269,c_43])).

cnf(c_11629,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11628])).

cnf(c_11636,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_11629])).

cnf(c_15423,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11636,c_43])).

cnf(c_15424,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15423])).

cnf(c_15431,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_15424])).

cnf(c_17106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15431,c_43])).

cnf(c_17107,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_17106])).

cnf(c_17114,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_17107])).

cnf(c_19560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17114,c_43])).

cnf(c_19561,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19560])).

cnf(c_19568,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_19561])).

cnf(c_23326,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19568,c_43])).

cnf(c_23327,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23326])).

cnf(c_23334,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_23327])).

cnf(c_27287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23334,c_43])).

cnf(c_27288,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27287])).

cnf(c_27295,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_27288])).

cnf(c_29952,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27295,c_43])).

cnf(c_29953,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_29952])).

cnf(c_29960,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_29953])).

cnf(c_31279,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29960,c_43])).

cnf(c_31280,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_31279])).

cnf(c_31287,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_31280])).

cnf(c_33920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31287,c_43])).

cnf(c_33921,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_33920])).

cnf(c_33928,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_33921])).

cnf(c_37889,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33928,c_43])).

cnf(c_37890,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37889])).

cnf(c_37897,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_37890])).

cnf(c_41532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37897,c_43])).

cnf(c_41533,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_41532])).

cnf(c_41540,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_41533])).

cnf(c_50624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41540,c_43])).

cnf(c_50625,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_50624])).

cnf(c_50632,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_50625])).

cnf(c_60220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50632,c_43])).

cnf(c_60221,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_60220])).

cnf(c_60228,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_60221])).

cnf(c_78479,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60228,c_43])).

cnf(c_78480,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_78479])).

cnf(c_78487,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_78480])).

cnf(c_99077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_78487,c_43])).

cnf(c_99078,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_99077])).

cnf(c_99085,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_99078])).

cnf(c_109651,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_99085,c_43])).

cnf(c_109652,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_109651])).

cnf(c_109660,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))))))))))))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4616,c_109652])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1971,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
    | v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,sK0(X0,X1,sK4))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2149,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_2150,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2149])).

cnf(c_33758,plain,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_33759,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33758])).

cnf(c_8370,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k7_relset_1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_72236,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_8370])).

cnf(c_108111,plain,
    ( r1_tarski(k7_relset_1(X0,X1,X2,X3),k7_relset_1(X0,X1,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_109876,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_108111])).

cnf(c_109878,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109876])).

cnf(c_109880,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109878])).

cnf(c_104702,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK0(X2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK0(X2,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK0(X2,sK3,sK4))) != X0
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK0(X2,sK3,sK4))) != X1 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_106224,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),X1)
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != X1 ),
    inference(instantiation,[status(thm)],[c_104702])).

cnf(c_109877,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))))
    | k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_106224])).

cnf(c_109882,plain,
    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109877])).

cnf(c_109884,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109882])).

cnf(c_109952,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_109660,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_2078,c_2150,c_2514,c_4616,c_5612,c_6015,c_6082,c_6124,c_6125,c_7787,c_9239,c_10049,c_10336,c_10338,c_17887,c_27629,c_33759,c_72236,c_109880,c_109884])).

cnf(c_111891,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10745,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_52,c_2070,c_2078,c_2123,c_2126,c_2150,c_2514,c_2791,c_2848,c_4616,c_5590,c_5612,c_6015,c_6082,c_6124,c_6125,c_7787,c_9239,c_10049,c_10336,c_10338,c_17887,c_27629,c_33759,c_72236,c_109880,c_109884])).

cnf(c_1260,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v3_tops_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3600,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1260])).

cnf(c_10117,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3600,c_1254,c_1255])).

cnf(c_10950,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10945,c_10117])).

cnf(c_11842,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10950,c_43,c_46,c_47,c_48,c_49])).

cnf(c_11848,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11842,c_6265])).

cnf(c_109958,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_109952,c_11848])).

cnf(c_110125,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_109958,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_2078,c_2150,c_2514,c_4616,c_5612,c_6015,c_6082,c_6124,c_6125,c_7787,c_9239,c_10049,c_10336,c_10338,c_11848,c_17887,c_27629,c_33759,c_72236,c_109880,c_109884])).

cnf(c_111893,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(light_normalisation,[status(thm)],[c_111891,c_110125])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1245,plain,
    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))
    | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
    | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v3_tops_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_111895,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_111893,c_1245])).

cnf(c_1250,plain,
    ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5249,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_1250])).

cnf(c_128,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1985,plain,
    ( l1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1979])).

cnf(c_3310,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3308])).

cnf(c_5748,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5249,c_40,c_39,c_36,c_35,c_34,c_128,c_1985,c_3064,c_3310,c_4101])).

cnf(c_111896,plain,
    ( k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_111895,c_5032,c_5748])).

cnf(c_111897,plain,
    ( k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_111896])).

cnf(c_10746,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_10731,c_5604])).

cnf(c_12186,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10746,c_10117])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_142211,c_111897,c_109952,c_28255,c_12186,c_6265,c_4101,c_3301,c_3062,c_2791,c_2126,c_2123,c_2078,c_2070,c_1979,c_129,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.76/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.76/6.99  
% 51.76/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.76/6.99  
% 51.76/6.99  ------  iProver source info
% 51.76/6.99  
% 51.76/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.76/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.76/6.99  git: non_committed_changes: false
% 51.76/6.99  git: last_make_outside_of_git: false
% 51.76/6.99  
% 51.76/6.99  ------ 
% 51.76/6.99  ------ Parsing...
% 51.76/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.76/6.99  
% 51.76/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 51.76/6.99  
% 51.76/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.76/6.99  
% 51.76/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.76/6.99  ------ Proving...
% 51.76/6.99  ------ Problem Properties 
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  clauses                                 38
% 51.76/6.99  conjectures                             14
% 51.76/6.99  EPR                                     10
% 51.76/6.99  Horn                                    25
% 51.76/6.99  unary                                   9
% 51.76/6.99  binary                                  4
% 51.76/6.99  lits                                    205
% 51.76/6.99  lits eq                                 26
% 51.76/6.99  fd_pure                                 0
% 51.76/6.99  fd_pseudo                               0
% 51.76/6.99  fd_cond                                 0
% 51.76/6.99  fd_pseudo_cond                          1
% 51.76/6.99  AC symbols                              0
% 51.76/6.99  
% 51.76/6.99  ------ Input Options Time Limit: Unbounded
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  ------ 
% 51.76/6.99  Current options:
% 51.76/6.99  ------ 
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  ------ Proving...
% 51.76/6.99  
% 51.76/6.99  
% 51.76/6.99  % SZS status Theorem for theBenchmark.p
% 51.76/6.99  
% 51.76/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.76/6.99  
% 51.76/6.99  fof(f12,conjecture,(
% 51.76/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f13,negated_conjecture,(
% 51.76/6.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 51.76/6.99    inference(negated_conjecture,[],[f12])).
% 51.76/6.99  
% 51.76/6.99  fof(f33,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 51.76/6.99    inference(ennf_transformation,[],[f13])).
% 51.76/6.99  
% 51.76/6.99  fof(f34,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f33])).
% 51.76/6.99  
% 51.76/6.99  fof(f48,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.76/6.99    inference(nnf_transformation,[],[f34])).
% 51.76/6.99  
% 51.76/6.99  fof(f49,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f48])).
% 51.76/6.99  
% 51.76/6.99  fof(f50,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 51.76/6.99    inference(rectify,[],[f49])).
% 51.76/6.99  
% 51.76/6.99  fof(f54,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f53,plain,(
% 51.76/6.99    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(sK4) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0) | ~v3_tops_2(sK4,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(sK4) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0)) | v3_tops_2(sK4,X0,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f52,plain,(
% 51.76/6.99    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,sK3)) & ((! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,sK3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f51,plain,(
% 51.76/6.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2) | ~v3_tops_2(X2,sK2,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2)) | v3_tops_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f55,plain,(
% 51.76/6.99    ((((k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)) & ((! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)) | v3_tops_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 51.76/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).
% 51.76/6.99  
% 51.76/6.99  fof(f93,plain,(
% 51.76/6.99    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | v3_tops_2(sK4,sK2,sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f91,plain,(
% 51.76/6.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f4,axiom,(
% 51.76/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f17,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f4])).
% 51.76/6.99  
% 51.76/6.99  fof(f18,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f17])).
% 51.76/6.99  
% 51.76/6.99  fof(f37,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(nnf_transformation,[],[f18])).
% 51.76/6.99  
% 51.76/6.99  fof(f38,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f37])).
% 51.76/6.99  
% 51.76/6.99  fof(f62,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f38])).
% 51.76/6.99  
% 51.76/6.99  fof(f85,plain,(
% 51.76/6.99    l1_pre_topc(sK2)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f88,plain,(
% 51.76/6.99    l1_pre_topc(sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f89,plain,(
% 51.76/6.99    v1_funct_1(sK4)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f90,plain,(
% 51.76/6.99    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f7,axiom,(
% 51.76/6.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f23,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f7])).
% 51.76/6.99  
% 51.76/6.99  fof(f24,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(flattening,[],[f23])).
% 51.76/6.99  
% 51.76/6.99  fof(f73,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f24])).
% 51.76/6.99  
% 51.76/6.99  fof(f86,plain,(
% 51.76/6.99    ~v2_struct_0(sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f3,axiom,(
% 51.76/6.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f16,plain,(
% 51.76/6.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f3])).
% 51.76/6.99  
% 51.76/6.99  fof(f60,plain,(
% 51.76/6.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f16])).
% 51.76/6.99  
% 51.76/6.99  fof(f63,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f38])).
% 51.76/6.99  
% 51.76/6.99  fof(f94,plain,(
% 51.76/6.99    v2_funct_1(sK4) | v3_tops_2(sK4,sK2,sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f11,axiom,(
% 51.76/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f31,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.76/6.99    inference(ennf_transformation,[],[f11])).
% 51.76/6.99  
% 51.76/6.99  fof(f32,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.76/6.99    inference(flattening,[],[f31])).
% 51.76/6.99  
% 51.76/6.99  fof(f43,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.76/6.99    inference(nnf_transformation,[],[f32])).
% 51.76/6.99  
% 51.76/6.99  fof(f44,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.76/6.99    inference(flattening,[],[f43])).
% 51.76/6.99  
% 51.76/6.99  fof(f45,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.76/6.99    inference(rectify,[],[f44])).
% 51.76/6.99  
% 51.76/6.99  fof(f46,plain,(
% 51.76/6.99    ! [X2,X1,X0] : (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f47,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.76/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 51.76/6.99  
% 51.76/6.99  fof(f82,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f47])).
% 51.76/6.99  
% 51.76/6.99  fof(f84,plain,(
% 51.76/6.99    v2_pre_topc(sK2)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f87,plain,(
% 51.76/6.99    v2_pre_topc(sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f5,axiom,(
% 51.76/6.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f19,plain,(
% 51.76/6.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.76/6.99    inference(ennf_transformation,[],[f5])).
% 51.76/6.99  
% 51.76/6.99  fof(f20,plain,(
% 51.76/6.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.76/6.99    inference(flattening,[],[f19])).
% 51.76/6.99  
% 51.76/6.99  fof(f67,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f20])).
% 51.76/6.99  
% 51.76/6.99  fof(f69,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f20])).
% 51.76/6.99  
% 51.76/6.99  fof(f68,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f20])).
% 51.76/6.99  
% 51.76/6.99  fof(f8,axiom,(
% 51.76/6.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f25,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f8])).
% 51.76/6.99  
% 51.76/6.99  fof(f26,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(flattening,[],[f25])).
% 51.76/6.99  
% 51.76/6.99  fof(f75,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f26])).
% 51.76/6.99  
% 51.76/6.99  fof(f74,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f24])).
% 51.76/6.99  
% 51.76/6.99  fof(f2,axiom,(
% 51.76/6.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f14,plain,(
% 51.76/6.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 51.76/6.99    inference(ennf_transformation,[],[f2])).
% 51.76/6.99  
% 51.76/6.99  fof(f15,plain,(
% 51.76/6.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f14])).
% 51.76/6.99  
% 51.76/6.99  fof(f59,plain,(
% 51.76/6.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f15])).
% 51.76/6.99  
% 51.76/6.99  fof(f9,axiom,(
% 51.76/6.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f27,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f9])).
% 51.76/6.99  
% 51.76/6.99  fof(f28,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 51.76/6.99    inference(flattening,[],[f27])).
% 51.76/6.99  
% 51.76/6.99  fof(f76,plain,(
% 51.76/6.99    ( ! [X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f28])).
% 51.76/6.99  
% 51.76/6.99  fof(f64,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f38])).
% 51.76/6.99  
% 51.76/6.99  fof(f61,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f38])).
% 51.76/6.99  
% 51.76/6.99  fof(f92,plain,(
% 51.76/6.99    k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) | v3_tops_2(sK4,sK2,sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f66,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f38])).
% 51.76/6.99  
% 51.76/6.99  fof(f96,plain,(
% 51.76/6.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f10,axiom,(
% 51.76/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f29,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(ennf_transformation,[],[f10])).
% 51.76/6.99  
% 51.76/6.99  fof(f30,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f29])).
% 51.76/6.99  
% 51.76/6.99  fof(f77,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f30])).
% 51.76/6.99  
% 51.76/6.99  fof(f81,plain,(
% 51.76/6.99    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f47])).
% 51.76/6.99  
% 51.76/6.99  fof(f1,axiom,(
% 51.76/6.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f35,plain,(
% 51.76/6.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.76/6.99    inference(nnf_transformation,[],[f1])).
% 51.76/6.99  
% 51.76/6.99  fof(f36,plain,(
% 51.76/6.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.76/6.99    inference(flattening,[],[f35])).
% 51.76/6.99  
% 51.76/6.99  fof(f58,plain,(
% 51.76/6.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f36])).
% 51.76/6.99  
% 51.76/6.99  fof(f57,plain,(
% 51.76/6.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 51.76/6.99    inference(cnf_transformation,[],[f36])).
% 51.76/6.99  
% 51.76/6.99  fof(f98,plain,(
% 51.76/6.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.76/6.99    inference(equality_resolution,[],[f57])).
% 51.76/6.99  
% 51.76/6.99  fof(f97,plain,(
% 51.76/6.99    k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f6,axiom,(
% 51.76/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 51.76/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.76/6.99  
% 51.76/6.99  fof(f21,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.76/6.99    inference(ennf_transformation,[],[f6])).
% 51.76/6.99  
% 51.76/6.99  fof(f22,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.76/6.99    inference(flattening,[],[f21])).
% 51.76/6.99  
% 51.76/6.99  fof(f39,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.76/6.99    inference(nnf_transformation,[],[f22])).
% 51.76/6.99  
% 51.76/6.99  fof(f40,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.76/6.99    inference(rectify,[],[f39])).
% 51.76/6.99  
% 51.76/6.99  fof(f41,plain,(
% 51.76/6.99    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 51.76/6.99    introduced(choice_axiom,[])).
% 51.76/6.99  
% 51.76/6.99  fof(f42,plain,(
% 51.76/6.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.76/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 51.76/6.99  
% 51.76/6.99  fof(f70,plain,(
% 51.76/6.99    ( ! [X4,X2,X0,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f42])).
% 51.76/6.99  
% 51.76/6.99  fof(f95,plain,(
% 51.76/6.99    ( ! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) | v3_tops_2(sK4,sK2,sK3)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f55])).
% 51.76/6.99  
% 51.76/6.99  fof(f71,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f42])).
% 51.76/6.99  
% 51.76/6.99  fof(f72,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f42])).
% 51.76/6.99  
% 51.76/6.99  fof(f83,plain,(
% 51.76/6.99    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.76/6.99    inference(cnf_transformation,[],[f47])).
% 51.76/6.99  
% 51.76/6.99  cnf(c_566,plain,
% 51.76/6.99      ( X0 != X1 | X2 != X3 | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
% 51.76/6.99      theory(equality) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_107143,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != X1
% 51.76/6.99      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(X2,X1)
% 51.76/6.99      | sK3 != X2 ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_566]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_110113,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != X1
% 51.76/6.99      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,X1)
% 51.76/6.99      | sK3 != sK3 ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_107143]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_142211,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 51.76/6.99      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/6.99      | sK3 != sK3 ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_110113]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_32,negated_conjecture,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/6.99      inference(cnf_transformation,[],[f93]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1238,plain,
% 51.76/6.99      ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_34,negated_conjecture,
% 51.76/6.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 51.76/6.99      inference(cnf_transformation,[],[f91]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1236,plain,
% 51.76/6.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_9,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f62]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1258,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X0,X1) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3784,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1236,c_1258]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_40,negated_conjecture,
% 51.76/6.99      ( l1_pre_topc(sK2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f85]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_43,plain,
% 51.76/6.99      ( l1_pre_topc(sK2) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_37,negated_conjecture,
% 51.76/6.99      ( l1_pre_topc(sK3) ),
% 51.76/6.99      inference(cnf_transformation,[],[f88]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_46,plain,
% 51.76/6.99      ( l1_pre_topc(sK3) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_36,negated_conjecture,
% 51.76/6.99      ( v1_funct_1(sK4) ),
% 51.76/6.99      inference(cnf_transformation,[],[f89]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_47,plain,
% 51.76/6.99      ( v1_funct_1(sK4) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_35,negated_conjecture,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 51.76/6.99      inference(cnf_transformation,[],[f90]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_48,plain,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4095,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_3784,c_43,c_46,c_47,c_48,c_49,c_2135]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4096,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_4095]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4101,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1238,c_4096]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_18,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | v2_struct_0(X2)
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | ~ l1_struct_0(X2)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f73]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1249,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) = k2_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2) != k2_struct_0(X0)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | v2_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_struct_0(X0) != iProver_top
% 51.76/6.99      | l1_struct_0(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4529,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(sK2) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_4101,c_1249]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_39,negated_conjecture,
% 51.76/6.99      ( ~ v2_struct_0(sK3) ),
% 51.76/6.99      inference(cnf_transformation,[],[f86]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_44,plain,
% 51.76/6.99      ( v2_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_49,plain,
% 51.76/6.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4,plain,
% 51.76/6.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 51.76/6.99      inference(cnf_transformation,[],[f60]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_127,plain,
% 51.76/6.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_129,plain,
% 51.76/6.99      ( l1_struct_0(sK2) = iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_127]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1233,plain,
% 51.76/6.99      ( l1_pre_topc(sK3) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1263,plain,
% 51.76/6.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1979,plain,
% 51.76/6.99      ( l1_struct_0(sK3) = iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1233,c_1263]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_8,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | v2_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f63]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1259,plain,
% 51.76/6.99      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/6.99      | v3_tops_2(X0,X1,X2) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/6.99      | v1_funct_1(X0) != iProver_top
% 51.76/6.99      | v2_funct_1(X0) = iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top
% 51.76/6.99      | l1_pre_topc(X2) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2848,plain,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) = iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1236,c_1259]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_31,negated_conjecture,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) | v2_funct_1(sK4) ),
% 51.76/6.99      inference(cnf_transformation,[],[f94]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_52,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/6.99      | v2_funct_1(sK4) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3062,plain,
% 51.76/6.99      ( v2_funct_1(sK4) = iProver_top ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_2848,c_43,c_46,c_47,c_48,c_52]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2285,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | v2_struct_0(X1)
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | ~ l1_struct_0(X0)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) = k2_struct_0(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_18]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3303,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 51.76/6.99      | v2_struct_0(sK3)
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(X0)
% 51.76/6.99      | ~ l1_struct_0(sK3)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_2285]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3304,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(X0) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_3303]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3306,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(sK2) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_3304]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5032,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_4529,c_40,c_39,c_36,c_35,c_34,c_128,c_1985,c_3064,
% 51.76/6.99                 c_3305,c_4101]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_23,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 51.76/6.99      | v2_struct_0(X1)
% 51.76/6.99      | ~ v2_pre_topc(X2)
% 51.76/6.99      | ~ v2_pre_topc(X1)
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f82]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1244,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X0,X1) = iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/6.99      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v2_pre_topc(X1) != iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | v2_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5035,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 51.76/6.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/6.99      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v2_pre_topc(sK2) != iProver_top
% 51.76/6.99      | v2_pre_topc(sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_5032,c_1244]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_41,negated_conjecture,
% 51.76/6.99      ( v2_pre_topc(sK2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f84]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_42,plain,
% 51.76/6.99      ( v2_pre_topc(sK2) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_38,negated_conjecture,
% 51.76/6.99      ( v2_pre_topc(sK3) ),
% 51.76/6.99      inference(cnf_transformation,[],[f87]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_45,plain,
% 51.76/6.99      ( v2_pre_topc(sK3) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_13,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 51.76/6.99      inference(cnf_transformation,[],[f67]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1853,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,X0,X1)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.76/6.99      | v1_funct_1(k2_tops_2(X0,X1,sK4))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_13]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2069,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1853]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2070,plain,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_2069]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_11,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.76/6.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.76/6.99      | ~ v1_funct_1(X0) ),
% 51.76/6.99      inference(cnf_transformation,[],[f69]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1858,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,X0,X1)
% 51.76/6.99      | m1_subset_1(k2_tops_2(X0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_11]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2122,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1858]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2123,plain,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_12,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,X1,X2)
% 51.76/6.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.76/6.99      | ~ v1_funct_1(X0) ),
% 51.76/6.99      inference(cnf_transformation,[],[f68]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1863,plain,
% 51.76/6.99      ( v1_funct_2(k2_tops_2(X0,X1,sK4),X1,X0)
% 51.76/6.99      | ~ v1_funct_2(sK4,X0,X1)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_12]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2125,plain,
% 51.76/6.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 51.76/6.99      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | ~ v1_funct_1(sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1863]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2126,plain,
% 51.76/6.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_19,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 51.76/6.99      | ~ l1_struct_0(X2)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f75]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2287,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4))
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | ~ l1_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_19]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3300,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(sK2)
% 51.76/6.99      | ~ l1_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_2287]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3301,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(sK2) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_3300]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_17,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | v2_struct_0(X2)
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | ~ l1_struct_0(X2)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 51.76/6.99      inference(cnf_transformation,[],[f74]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2286,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | v2_struct_0(X1)
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | ~ l1_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) = k2_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_17]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3308,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3))
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
% 51.76/6.99      | v2_struct_0(sK3)
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | ~ l1_struct_0(X0)
% 51.76/6.99      | ~ l1_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(X0) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_2286]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3309,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),sK4)) = k2_struct_0(X0)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(X0) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_3308]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3311,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(sK2) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_3309]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3032,plain,
% 51.76/6.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
% 51.76/6.99      | m1_subset_1(sK1(X0,X1,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/6.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | v2_struct_0(X0)
% 51.76/6.99      | ~ v2_pre_topc(X1)
% 51.76/6.99      | ~ v2_pre_topc(X0)
% 51.76/6.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ l1_pre_topc(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_23]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4742,plain,
% 51.76/6.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(X0))
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,X0)
% 51.76/6.99      | m1_subset_1(sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0)))
% 51.76/6.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 51.76/6.99      | v2_struct_0(sK3)
% 51.76/6.99      | ~ v2_pre_topc(X0)
% 51.76/6.99      | ~ v2_pre_topc(sK3)
% 51.76/6.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ l1_pre_topc(X0)
% 51.76/6.99      | ~ l1_pre_topc(sK3)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_3032]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4743,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(X0)
% 51.76/6.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,X0) = iProver_top
% 51.76/6.99      | m1_subset_1(sK1(sK3,X0,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v2_pre_topc(sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4745,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 51.76/6.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/6.99      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v2_pre_topc(sK2) != iProver_top
% 51.76/6.99      | v2_pre_topc(sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_4743]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_10731,plain,
% 51.76/6.99      ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/6.99      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_5035,c_42,c_40,c_43,c_39,c_44,c_45,c_46,c_36,c_47,
% 51.76/6.99                 c_35,c_48,c_34,c_49,c_52,c_128,c_129,c_1979,c_1985,
% 51.76/6.99                 c_2070,c_2123,c_2126,c_2848,c_3064,c_3301,c_3305,c_3310,
% 51.76/6.99                 c_4101,c_4745]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3,plain,
% 51.76/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/6.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/6.99      | ~ l1_pre_topc(X1) ),
% 51.76/6.99      inference(cnf_transformation,[],[f59]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1264,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_20,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | ~ l1_struct_0(X2)
% 51.76/6.99      | ~ l1_struct_0(X1)
% 51.76/6.99      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f76]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1247,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2,X3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),X2) != k2_struct_0(X0)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | v2_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_struct_0(X0) != iProver_top
% 51.76/6.99      | l1_struct_0(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5235,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_struct_0(sK2) != iProver_top
% 51.76/6.99      | l1_struct_0(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_4101,c_1247]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5603,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_5235,c_43,c_46,c_47,c_48,c_49,c_52,c_129,c_1979,
% 51.76/6.99                 c_2848]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5604,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_5603]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5611,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_5604]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6006,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_5611,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6007,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_6006]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_10745,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_10731,c_6007]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_7,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | v5_pre_topc(X0,X1,X2)
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f64]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2206,plain,
% 51.76/6.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
% 51.76/6.99      | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0,X1)
% 51.76/6.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ l1_pre_topc(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_7]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2790,plain,
% 51.76/6.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 51.76/6.99      | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 51.76/6.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 51.76/6.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/6.99      | ~ l1_pre_topc(sK2)
% 51.76/6.99      | ~ l1_pre_topc(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_2206]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2791,plain,
% 51.76/6.99      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_2790]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_10,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
% 51.76/6.99      inference(cnf_transformation,[],[f61]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1257,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X0,X1) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3645,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1236,c_1257]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_33,negated_conjecture,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f92]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_50,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3957,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_3645,c_43,c_46,c_47,c_48,c_50]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v5_pre_topc(X0,X1,X2)
% 51.76/6.99      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 51.76/6.99      | v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ v2_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f66]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1262,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v5_pre_topc(X2,X0,X1) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X0,X1) = iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | v2_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5557,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/6.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_3957,c_1262]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5589,plain,
% 51.76/6.99      ( k2_struct_0(sK3) != k2_struct_0(sK3)
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/6.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(light_normalisation,[status(thm)],[c_5557,c_4101]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_5590,plain,
% 51.76/6.99      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/6.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/6.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(equality_resolution_simp,[status(thm)],[c_5589]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6264,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/6.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_5590,c_43,c_46,c_47,c_48,c_49,c_52,c_2848]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6265,plain,
% 51.76/6.99      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/6.99      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_6264]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_29,negated_conjecture,
% 51.76/6.99      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/6.99      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/6.99      inference(cnf_transformation,[],[f96]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1241,plain,
% 51.76/6.99      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/6.99      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3960,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | k2_struct_0(sK2) != k2_struct_0(sK2)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(demodulation,[status(thm)],[c_3957,c_1241]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4082,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | v2_funct_1(sK4) != iProver_top ),
% 51.76/6.99      inference(equality_resolution_simp,[status(thm)],[c_3960]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_564,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2586,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | k2_struct_0(sK3) = X0 ),
% 51.76/6.99      inference(resolution,[status(thm)],[c_564,c_32]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1822,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != X0
% 51.76/6.99      | k2_struct_0(sK3) != X0
% 51.76/6.99      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_564]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2054,plain,
% 51.76/6.99      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/6.99      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1822]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_563,plain,( X0 = X0 ),theory(equality) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2055,plain,
% 51.76/6.99      ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_563]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1918,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | ~ v3_tops_2(sK4,X0,X1)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ l1_pre_topc(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_9]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2134,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ l1_pre_topc(sK2)
% 51.76/6.99      | ~ l1_pre_topc(sK3)
% 51.76/6.99      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1918]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2056,plain,
% 51.76/6.99      ( X0 != X1 | k2_struct_0(sK3) != X1 | k2_struct_0(sK3) = X0 ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_564]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2642,plain,
% 51.76/6.99      ( X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | k2_struct_0(sK3) = X0
% 51.76/6.99      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_2056]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2918,plain,
% 51.76/6.99      ( X0 != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/6.99      | k2_struct_0(sK3) = X0 ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_2586,c_40,c_37,c_36,c_35,c_34,c_2054,c_2055,c_2134,
% 51.76/6.99                 c_2642]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2935,plain,
% 51.76/6.99      ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/6.99      inference(resolution,[status(thm)],[c_2918,c_563]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3364,plain,
% 51.76/6.99      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/6.99      | ~ v2_funct_1(sK4)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) ),
% 51.76/6.99      inference(backward_subsumption_resolution,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_2935,c_29]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1923,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/6.99      | ~ v3_tops_2(sK4,X0,X1)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ l1_pre_topc(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_10]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2137,plain,
% 51.76/6.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/6.99      | ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/6.99      | ~ v1_funct_1(sK4)
% 51.76/6.99      | ~ l1_pre_topc(sK2)
% 51.76/6.99      | ~ l1_pre_topc(sK3)
% 51.76/6.99      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 51.76/6.99      inference(instantiation,[status(thm)],[c_1923]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3064,plain,
% 51.76/6.99      ( v2_funct_1(sK4) ),
% 51.76/6.99      inference(predicate_to_equality_rev,[status(thm)],[c_3062]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3501,plain,
% 51.76/6.99      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_3364,c_40,c_37,c_36,c_35,c_34,c_29,c_2137,c_2935,
% 51.76/6.99                 c_3064]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_3503,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_3501]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4084,plain,
% 51.76/6.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_4082,c_3503]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_4085,plain,
% 51.76/6.99      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_4084]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | v2_struct_0(X2)
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2) ),
% 51.76/6.99      inference(cnf_transformation,[],[f77]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1246,plain,
% 51.76/6.99      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/6.99      | v3_tops_2(X0,X1,X2) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/6.99      | v2_struct_0(X2) = iProver_top
% 51.76/6.99      | v1_funct_1(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top
% 51.76/6.99      | l1_pre_topc(X2) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1256,plain,
% 51.76/6.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.76/6.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 51.76/6.99      | v1_funct_1(X0) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_24,plain,
% 51.76/6.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/6.99      | ~ v3_tops_2(X0,X1,X2)
% 51.76/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/6.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 51.76/6.99      | v2_struct_0(X1)
% 51.76/6.99      | ~ v2_pre_topc(X2)
% 51.76/6.99      | ~ v2_pre_topc(X1)
% 51.76/6.99      | ~ v1_funct_1(X0)
% 51.76/6.99      | ~ l1_pre_topc(X1)
% 51.76/6.99      | ~ l1_pre_topc(X2)
% 51.76/6.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) ),
% 51.76/6.99      inference(cnf_transformation,[],[f81]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1243,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X0,X1) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/6.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v2_pre_topc(X1) != iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_2697,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v2_pre_topc(X1) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2)) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1256,c_1243]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1254,plain,
% 51.76/6.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.76/6.99      | v1_funct_1(X0) != iProver_top
% 51.76/6.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_1255,plain,
% 51.76/6.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 51.76/6.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.76/6.99      | v1_funct_1(X0) != iProver_top ),
% 51.76/6.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6287,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X0,X1) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v2_pre_topc(X1) != iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.76/6.99      inference(forward_subsumption_resolution,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_2697,c_1254,c_1255]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_6291,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),X2),X3))
% 51.76/6.99      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 51.76/6.99      | v3_tops_2(X2,X1,X0) != iProver_top
% 51.76/6.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 51.76/6.99      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 51.76/6.99      | v2_struct_0(X0) = iProver_top
% 51.76/6.99      | v2_pre_topc(X0) != iProver_top
% 51.76/6.99      | v2_pre_topc(X1) != iProver_top
% 51.76/6.99      | v1_funct_1(X2) != iProver_top
% 51.76/6.99      | l1_pre_topc(X1) != iProver_top
% 51.76/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1246,c_6287]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_19254,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
% 51.76/6.99      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v2_struct_0(sK3) = iProver_top
% 51.76/6.99      | v2_pre_topc(sK2) != iProver_top
% 51.76/6.99      | v2_pre_topc(sK3) != iProver_top
% 51.76/6.99      | v1_funct_1(sK4) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1236,c_6291]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_19900,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_19254,c_42,c_43,c_44,c_45,c_46,c_47,c_48]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_19909,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_19900]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_20083,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_19909,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_20084,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_20083]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_20092,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_20084]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21093,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_20092,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21094,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_21093]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21102,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_21094]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21149,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_21102,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21150,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_21149]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21158,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_21150]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21379,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_21158,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21380,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_21379]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21388,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_21380]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21435,plain,
% 51.76/6.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) ),
% 51.76/6.99      inference(global_propositional_subsumption,
% 51.76/6.99                [status(thm)],
% 51.76/6.99                [c_21388,c_43]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21436,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/6.99      inference(renaming,[status(thm)],[c_21435]) ).
% 51.76/6.99  
% 51.76/6.99  cnf(c_21444,plain,
% 51.76/6.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
% 51.76/6.99      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/6.99      inference(superposition,[status(thm)],[c_1264,c_21436]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_21654,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_21444,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_21655,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_21654]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_21663,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_21655]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_22999,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_21663,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_23000,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_22999]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_23008,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_23000]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_25115,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_23008,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_25116,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_25115]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_25124,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_25116]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27501,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_25124,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27502,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_27501]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27511,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK5))))))))))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK5)))))))))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4085,c_27502]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2078,plain,
% 51.76/7.00      ( sK3 = sK3 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_563]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2514,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_563]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_5612,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4085,c_5604]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6015,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4085,c_6007]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2519,plain,
% 51.76/7.00      ( X0 != X1
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X1
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_564]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4289,plain,
% 51.76/7.00      ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = X0
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2519]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6082,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_4289]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_0,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 51.76/7.00      inference(cnf_transformation,[],[f58]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3925,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 51.76/7.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),X0)
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_0]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6124,plain,
% 51.76/7.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_3925]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1,plain,
% 51.76/7.00      ( r1_tarski(X0,X0) ),
% 51.76/7.00      inference(cnf_transformation,[],[f98]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4585,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(X0,X1,X2,X3),k7_relset_1(X0,X1,X2,X3)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6125,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_4585]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_28,negated_conjecture,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ v2_funct_1(sK4)
% 51.76/7.00      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 51.76/7.00      inference(cnf_transformation,[],[f97]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3365,plain,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ v2_funct_1(sK4)
% 51.76/7.00      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(backward_subsumption_resolution,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_2935,c_28]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1242,plain,
% 51.76/7.00      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | v2_funct_1(sK4) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_57,plain,
% 51.76/7.00      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | v2_funct_1(sK4) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1908,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/7.00      | ~ v3_tops_2(sK4,X0,X1)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | v2_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_8]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2128,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | v2_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1908]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2129,plain,
% 51.76/7.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | v2_funct_1(sK4) = iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_2128]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2135,plain,
% 51.76/7.00      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_2134]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2138,plain,
% 51.76/7.00      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_2137]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2153,plain,
% 51.76/7.00      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_1242,c_43,c_46,c_47,c_48,c_49,c_57,c_2054,c_2055,
% 51.76/7.00                 c_2129,c_2135,c_2138]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2154,plain,
% 51.76/7.00      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_2153]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2155,plain,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_2154]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4378,plain,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_3365,c_2155]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4394,plain,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
% 51.76/7.00      | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) ),
% 51.76/7.00      inference(resolution,[status(thm)],[c_4378,c_0]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1814,plain,
% 51.76/7.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
% 51.76/7.00      | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_0]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1913,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/7.00      | v5_pre_topc(sK4,X0,X1)
% 51.76/7.00      | ~ v3_tops_2(sK4,X0,X1)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_7]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2131,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3)
% 51.76/7.00      | ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1913]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_16,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/7.00      | ~ v5_pre_topc(X0,X1,X2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 51.76/7.00      | v2_struct_0(X2)
% 51.76/7.00      | ~ v2_pre_topc(X2)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(X2) ),
% 51.76/7.00      inference(cnf_transformation,[],[f70]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2375,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 51.76/7.00      | ~ v5_pre_topc(X0,sK2,X1)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 51.76/7.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,k2_pre_topc(sK2,sK5)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X0,sK5)))
% 51.76/7.00      | v2_struct_0(X1)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(sK2) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2950,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v2_pre_topc(sK3)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2375]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_7785,plain,
% 51.76/7.00      ( ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_4394,c_41,c_40,c_43,c_39,c_38,c_37,c_46,c_36,c_47,
% 51.76/7.00                 c_35,c_48,c_34,c_50,c_29,c_1814,c_2131,c_2155,c_2935,
% 51.76/7.00                 c_2950,c_3064,c_3645]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_7787,plain,
% 51.76/7.00      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_7785]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3931,plain,
% 51.76/7.00      ( X0 != X1
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X1
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_564]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6257,plain,
% 51.76/7.00      ( X0 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = X0
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_3931]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_9239,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_6257]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2046,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(X1,X0)
% 51.76/7.00      | sK3 != X1 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_566]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2639,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != X0
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,X0)
% 51.76/7.00      | sK3 != sK3 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2046]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10049,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | sK3 != sK3 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2639]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_565,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.76/7.00      theory(equality) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2019,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,X1)
% 51.76/7.00      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != X1
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_565]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6557,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10334,plain,
% 51.76/7.00      ( ~ r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_6557]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10336,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) != iProver_top
% 51.76/7.00      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))) = iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_10334]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10335,plain,
% 51.76/7.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10338,plain,
% 51.76/7.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))) = iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_10335]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_30,negated_conjecture,
% 51.76/7.00      ( v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
% 51.76/7.00      inference(cnf_transformation,[],[f95]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1240,plain,
% 51.76/7.00      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10750,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_10731,c_1240]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1933,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4),X1,X0)
% 51.76/7.00      | ~ v3_tops_2(sK4,X0,X1)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/7.00      | v2_struct_0(X1)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_21]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2143,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 51.76/7.00      | ~ v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1933]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2144,plain,
% 51.76/7.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_2143]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10944,plain,
% 51.76/7.00      ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_10750,c_43,c_44,c_46,c_47,c_48,c_49,c_2144]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10945,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_10944]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10952,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_10945,c_6287]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11991,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_10952,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11992,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_11991]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_12001,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4085,c_11992]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_56,plain,
% 51.76/7.00      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 51.76/7.00      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/7.00      | v2_funct_1(sK4) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2385,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
% 51.76/7.00      | ~ v3_tops_2(X0,X1,sK2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
% 51.76/7.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | v2_struct_0(X1)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK5)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(sK2),X0,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_24]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2956,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 51.76/7.00      | ~ v3_tops_2(X0,sK3,sK2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 51.76/7.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v2_pre_topc(sK3)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3)
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2385]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3562,plain,
% 51.76/7.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 51.76/7.00      | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 51.76/7.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 51.76/7.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v2_pre_topc(sK3)
% 51.76/7.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3)
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2956]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3563,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 51.76/7.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/7.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_3562]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_17887,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_12001,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,
% 51.76/7.00                 c_52,c_56,c_2070,c_2123,c_2126,c_2144,c_2848,c_2935,
% 51.76/7.00                 c_3563,c_3645]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2044,plain,
% 51.76/7.00      ( X0 != X1
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != X1
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = X0 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_564]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_15945,plain,
% 51.76/7.00      ( X0 != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = X0
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_2044]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27629,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_15945]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_28255,plain,
% 51.76/7.00      ( v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_27511,c_2078,c_2514,c_5612,c_6015,c_6082,c_6124,
% 51.76/7.00                 c_6125,c_7787,c_9239,c_10049,c_10336,c_10338,c_17887,
% 51.76/7.00                 c_27629]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_15,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/7.00      | v5_pre_topc(X0,X1,X2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/7.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 51.76/7.00      | v2_struct_0(X2)
% 51.76/7.00      | ~ v2_pre_topc(X2)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(X2) ),
% 51.76/7.00      inference(cnf_transformation,[],[f71]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1252,plain,
% 51.76/7.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/7.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/7.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 51.76/7.00      | v2_struct_0(X2) = iProver_top
% 51.76/7.00      | v2_pre_topc(X2) != iProver_top
% 51.76/7.00      | v2_pre_topc(X1) != iProver_top
% 51.76/7.00      | v1_funct_1(X0) != iProver_top
% 51.76/7.00      | l1_pre_topc(X1) != iProver_top
% 51.76/7.00      | l1_pre_topc(X2) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4472,plain,
% 51.76/7.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 51.76/7.00      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1236,c_1252]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_4616,plain,
% 51.76/7.00      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 51.76/7.00      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_4472,c_42,c_43,c_44,c_45,c_46,c_47,c_48]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6014,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_6007]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6477,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_6014,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6478,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_6477]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6485,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_6478]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6508,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_6485,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6509,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_6508]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6516,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_6509]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6634,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_6516,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6635,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_6634]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_6642,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_6635]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_7553,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_6642,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_7554,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_7553]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_7561,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_7554]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_8884,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_7561,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_8885,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_8884]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_8892,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_8885]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10261,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_8892,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10262,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_10261]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10269,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_10262]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11628,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_10269,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11629,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_11628]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11636,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_11629]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_15423,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_11636,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_15424,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_15423]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_15431,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_15424]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_17106,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_15431,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_17107,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_17106]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_17114,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_17107]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_19560,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_17114,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_19561,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_19560]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_19568,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_19561]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_23326,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_19568,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_23327,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_23326]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_23334,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_23327]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27287,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_23334,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27288,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_27287]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_27295,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_27288]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_29952,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_27295,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_29953,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_29952]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_29960,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_29953]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_31279,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_29960,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_31280,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_31279]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_31287,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_31280]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_33920,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_31287,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_33921,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_33920]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_33928,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_33921]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_37889,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_33928,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_37890,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_37889]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_37897,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_37890]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_41532,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_37897,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_41533,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_41532]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_41540,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_41533]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_50624,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_41540,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_50625,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_50624]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_50632,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_50625]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_60220,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_50632,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_60221,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_60220]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_60228,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_60221]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_78479,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_60228,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_78480,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_78479]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_78487,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_78480]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_99077,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_78487,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_99078,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_99077]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_99085,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1264,c_99078]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109651,plain,
% 51.76/7.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 51.76/7.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_99085,c_43]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109652,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0)))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0))))))))))))))))))))))))
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(renaming,[status(thm)],[c_109651]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109660,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))))))))))))))))))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))))))))))))))))))
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4616,c_109652]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_14,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/7.00      | v5_pre_topc(X0,X1,X2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/7.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
% 51.76/7.00      | v2_struct_0(X2)
% 51.76/7.00      | ~ v2_pre_topc(X2)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(X2) ),
% 51.76/7.00      inference(cnf_transformation,[],[f72]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1971,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
% 51.76/7.00      | v5_pre_topc(sK4,X0,X1)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 51.76/7.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,sK0(X0,X1,sK4))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4))))
% 51.76/7.00      | v2_struct_0(X1)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v2_pre_topc(X0)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_14]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2149,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v2_pre_topc(sK2)
% 51.76/7.00      | ~ v2_pre_topc(sK3)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ l1_pre_topc(sK2)
% 51.76/7.00      | ~ l1_pre_topc(sK3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1971]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_2150,plain,
% 51.76/7.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_2149]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_33758,plain,
% 51.76/7.00      ( v3_tops_2(sK4,sK2,sK3)
% 51.76/7.00      | ~ m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_30]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_33759,plain,
% 51.76/7.00      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 51.76/7.00      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_33758]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_8370,plain,
% 51.76/7.00      ( k7_relset_1(X0,X1,X2,X3) = k7_relset_1(X0,X1,X2,X3) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_563]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_72236,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_8370]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_108111,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(X0,X1,X2,X3),k7_relset_1(X0,X1,X2,X3)) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_1]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109876,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_108111]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109878,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) = iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_109876]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109880,plain,
% 51.76/7.00      ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))) = iProver_top ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_109878]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_104702,plain,
% 51.76/7.00      ( ~ r1_tarski(X0,X1)
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK0(X2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK0(X2,sK3,sK4))))
% 51.76/7.00      | k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,k2_pre_topc(X2,sK0(X2,sK3,sK4))) != X0
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X2),u1_struct_0(sK3),sK4,sK0(X2,sK3,sK4))) != X1 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_565]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_106224,plain,
% 51.76/7.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),X1)
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))))
% 51.76/7.00      | k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != X1 ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_104702]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109877,plain,
% 51.76/7.00      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))))
% 51.76/7.00      | k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_106224]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109882,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4))) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4)))) != iProver_top
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,k2_pre_topc(X0,sK0(X0,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),sK4,sK0(X0,sK3,sK4)))) = iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_109877]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109884,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 51.76/7.00      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))) != iProver_top
% 51.76/7.00      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_109882]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109952,plain,
% 51.76/7.00      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_109660,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_2078,
% 51.76/7.00                 c_2150,c_2514,c_4616,c_5612,c_6015,c_6082,c_6124,c_6125,
% 51.76/7.00                 c_7787,c_9239,c_10049,c_10336,c_10338,c_17887,c_27629,
% 51.76/7.00                 c_33759,c_72236,c_109880,c_109884]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_111891,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_10745,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_52,
% 51.76/7.00                 c_2070,c_2078,c_2123,c_2126,c_2150,c_2514,c_2791,c_2848,
% 51.76/7.00                 c_4616,c_5590,c_5612,c_6015,c_6082,c_6124,c_6125,c_7787,
% 51.76/7.00                 c_9239,c_10049,c_10336,c_10338,c_17887,c_27629,c_33759,
% 51.76/7.00                 c_72236,c_109880,c_109884]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1260,plain,
% 51.76/7.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/7.00      | v5_pre_topc(X0,X1,X2) = iProver_top
% 51.76/7.00      | v3_tops_2(X0,X1,X2) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/7.00      | v1_funct_1(X0) != iProver_top
% 51.76/7.00      | l1_pre_topc(X1) != iProver_top
% 51.76/7.00      | l1_pre_topc(X2) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3600,plain,
% 51.76/7.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/7.00      | v1_funct_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 51.76/7.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/7.00      | v1_funct_1(X0) != iProver_top
% 51.76/7.00      | v1_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) != iProver_top
% 51.76/7.00      | l1_pre_topc(X1) != iProver_top
% 51.76/7.00      | l1_pre_topc(X2) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_1256,c_1260]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10117,plain,
% 51.76/7.00      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 51.76/7.00      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) = iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1) != iProver_top
% 51.76/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 51.76/7.00      | v1_funct_1(X0) != iProver_top
% 51.76/7.00      | l1_pre_topc(X1) != iProver_top
% 51.76/7.00      | l1_pre_topc(X2) != iProver_top ),
% 51.76/7.00      inference(forward_subsumption_resolution,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_3600,c_1254,c_1255]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10950,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_10945,c_10117]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11842,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_10950,c_43,c_46,c_47,c_48,c_49]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_11848,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_11842,c_6265]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_109958,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_109952,c_11848]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_110125,plain,
% 51.76/7.00      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_109958,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_2078,
% 51.76/7.00                 c_2150,c_2514,c_4616,c_5612,c_6015,c_6082,c_6124,c_6125,
% 51.76/7.00                 c_7787,c_9239,c_10049,c_10336,c_10338,c_11848,c_17887,
% 51.76/7.00                 c_27629,c_33759,c_72236,c_109880,c_109884]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_111893,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 51.76/7.00      inference(light_normalisation,[status(thm)],[c_111891,c_110125]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_22,plain,
% 51.76/7.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.76/7.00      | v3_tops_2(X0,X1,X2)
% 51.76/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.76/7.00      | v2_struct_0(X1)
% 51.76/7.00      | ~ v2_pre_topc(X2)
% 51.76/7.00      | ~ v2_pre_topc(X1)
% 51.76/7.00      | ~ v1_funct_1(X0)
% 51.76/7.00      | ~ v2_funct_1(X0)
% 51.76/7.00      | ~ l1_pre_topc(X1)
% 51.76/7.00      | ~ l1_pre_topc(X2)
% 51.76/7.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)))
% 51.76/7.00      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 51.76/7.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 51.76/7.00      inference(cnf_transformation,[],[f83]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1245,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2)))
% 51.76/7.00      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
% 51.76/7.00      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 51.76/7.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/7.00      | v3_tops_2(X2,X0,X1) = iProver_top
% 51.76/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/7.00      | v2_struct_0(X0) = iProver_top
% 51.76/7.00      | v2_pre_topc(X1) != iProver_top
% 51.76/7.00      | v2_pre_topc(X0) != iProver_top
% 51.76/7.00      | v1_funct_1(X2) != iProver_top
% 51.76/7.00      | v2_funct_1(X2) != iProver_top
% 51.76/7.00      | l1_pre_topc(X0) != iProver_top
% 51.76/7.00      | l1_pre_topc(X1) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_111895,plain,
% 51.76/7.00      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 51.76/7.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 51.76/7.00      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_111893,c_1245]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1250,plain,
% 51.76/7.00      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
% 51.76/7.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
% 51.76/7.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 51.76/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 51.76/7.00      | v2_struct_0(X1) = iProver_top
% 51.76/7.00      | v1_funct_1(X2) != iProver_top
% 51.76/7.00      | v2_funct_1(X2) != iProver_top
% 51.76/7.00      | l1_struct_0(X1) != iProver_top
% 51.76/7.00      | l1_struct_0(X0) != iProver_top ),
% 51.76/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_5249,plain,
% 51.76/7.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | v2_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_struct_0(sK2) != iProver_top
% 51.76/7.00      | l1_struct_0(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_4101,c_1250]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_128,plain,
% 51.76/7.00      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_4]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_1985,plain,
% 51.76/7.00      ( l1_struct_0(sK3) ),
% 51.76/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_1979]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_3310,plain,
% 51.76/7.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 51.76/7.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 51.76/7.00      | v2_struct_0(sK3)
% 51.76/7.00      | ~ v1_funct_1(sK4)
% 51.76/7.00      | ~ v2_funct_1(sK4)
% 51.76/7.00      | ~ l1_struct_0(sK2)
% 51.76/7.00      | ~ l1_struct_0(sK3)
% 51.76/7.00      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 51.76/7.00      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
% 51.76/7.00      inference(instantiation,[status(thm)],[c_3308]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_5748,plain,
% 51.76/7.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
% 51.76/7.00      inference(global_propositional_subsumption,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_5249,c_40,c_39,c_36,c_35,c_34,c_128,c_1985,c_3064,
% 51.76/7.00                 c_3310,c_4101]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_111896,plain,
% 51.76/7.00      ( k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | k2_struct_0(sK2) != k2_struct_0(sK2)
% 51.76/7.00      | k2_struct_0(sK3) != k2_struct_0(sK3)
% 51.76/7.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(light_normalisation,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_111895,c_5032,c_5748]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_111897,plain,
% 51.76/7.00      ( k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 51.76/7.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 51.76/7.00      | v2_struct_0(sK3) = iProver_top
% 51.76/7.00      | v2_pre_topc(sK2) != iProver_top
% 51.76/7.00      | v2_pre_topc(sK3) != iProver_top
% 51.76/7.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(equality_resolution_simp,[status(thm)],[c_111896]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_10746,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 51.76/7.00      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_10731,c_5604]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(c_12186,plain,
% 51.76/7.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 51.76/7.00      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 51.76/7.00      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 51.76/7.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 51.76/7.00      | v1_funct_1(sK4) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK2) != iProver_top
% 51.76/7.00      | l1_pre_topc(sK3) != iProver_top ),
% 51.76/7.00      inference(superposition,[status(thm)],[c_10746,c_10117]) ).
% 51.76/7.00  
% 51.76/7.00  cnf(contradiction,plain,
% 51.76/7.00      ( $false ),
% 51.76/7.00      inference(minisat,
% 51.76/7.00                [status(thm)],
% 51.76/7.00                [c_142211,c_111897,c_109952,c_28255,c_12186,c_6265,
% 51.76/7.00                 c_4101,c_3301,c_3062,c_2791,c_2126,c_2123,c_2078,c_2070,
% 51.76/7.00                 c_1979,c_129,c_49,c_48,c_47,c_46,c_45,c_44,c_43,c_42]) ).
% 51.76/7.00  
% 51.76/7.00  
% 51.76/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.76/7.00  
% 51.76/7.00  ------                               Statistics
% 51.76/7.00  
% 51.76/7.00  ------ Selected
% 51.76/7.00  
% 51.76/7.00  total_time:                             6.463
% 51.76/7.00  
%------------------------------------------------------------------------------
