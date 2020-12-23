%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:52 EST 2020

% Result     : Theorem 48.04s
% Output     : CNFRefutation 48.04s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2883)

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f68,plain,(
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

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,
    ( k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f71,plain,(
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
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,
    ( v2_funct_1(sK4)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

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
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f72,plain,(
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

fof(f69,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f73,plain,(
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

fof(f67,plain,(
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

fof(f63,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f80,plain,(
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

fof(f81,plain,(
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

fof(f93,plain,(
    ! [X4] :
      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_tops_2(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
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

fof(f95,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | ~ v2_funct_1(sK4)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | ~ v3_tops_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1554,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2344,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1554])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_732,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_37])).

cnf(c_733,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_737,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_36,c_35])).

cnf(c_738,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1140,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_738,c_39])).

cnf(c_1141,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1140])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1145,plain,
    ( ~ v1_funct_1(X0)
    | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_38])).

cnf(c_1146,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1145])).

cnf(c_1539,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0_55,sK2,sK3)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK2,sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1146])).

cnf(c_2359,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(X0_55,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1539])).

cnf(c_4102,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2359])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4131,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4102,c_45,c_46])).

cnf(c_4132,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4131])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1574,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_57)))
    | m1_subset_1(k2_pre_topc(X0_57,X0_55),k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2324,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_57,X0_55),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1568,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2330,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X1_57)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v3_tops_2(X0_55,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_3722,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2330])).

cnf(c_30,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1556,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1579,plain,
    ( X0_59 != X1_59
    | X2_59 != X1_59
    | X2_59 = X0_59 ),
    theory(equality)).

cnf(c_3085,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != X0_59
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != X0_59 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_3231,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_3085])).

cnf(c_3232,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_3231])).

cnf(c_1577,plain,
    ( X0_59 = X0_59 ),
    theory(equality)).

cnf(c_3252,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_3754,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3722])).

cnf(c_3921,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3722,c_38,c_35,c_34,c_33,c_1556,c_3232,c_3252,c_3754])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_666,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_37])).

cnf(c_667,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_1547,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_667])).

cnf(c_2351,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_44,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1666,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1573,plain,
    ( l1_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2899,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_2900,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2899])).

cnf(c_3624,plain,
    ( l1_struct_0(X0_57) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2351,c_44,c_1666,c_2900])).

cnf(c_3625,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_3624])).

cnf(c_3926,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3921,c_3625])).

cnf(c_129,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1569,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | v2_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2329,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v3_tops_2(X0_55,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_3328,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_2329])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_29,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_50,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3426,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3328,c_41,c_44,c_45,c_46,c_50])).

cnf(c_3428,plain,
    ( v2_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3426])).

cnf(c_3626,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3625])).

cnf(c_3628,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3626])).

cnf(c_4600,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3926,c_38,c_35,c_34,c_33,c_32,c_129,c_1556,c_3232,c_3252,c_3428,c_3628,c_3754])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1561,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_57)))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
    | k7_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2337,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
    | k7_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_57))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_4603,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4600,c_2337])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_128,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_130,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1564,plain,
    ( ~ v1_funct_2(X0_55,X0_56,X1_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tops_2(X0_56,X1_56,X0_55)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2936,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_2937,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2936])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1565,plain,
    ( ~ v1_funct_2(X0_55,X0_56,X1_56)
    | v1_funct_2(k2_tops_2(X0_56,X1_56,X0_55),X1_56,X0_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2939,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_2940,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2939])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1566,plain,
    ( ~ v1_funct_2(X0_55,X0_56,X1_56)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2942,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_2943,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2942])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1563,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55))
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3091,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_3092,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3091])).

cnf(c_8409,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4603,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_47,c_50,c_130,c_1556,c_2900,c_2937,c_2940,c_2943,c_3092,c_3232,c_3252,c_3328,c_3754])).

cnf(c_8410,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8409])).

cnf(c_8418,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8410])).

cnf(c_8454,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8418,c_41])).

cnf(c_8455,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8454])).

cnf(c_8463,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8455])).

cnf(c_8621,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8463,c_41])).

cnf(c_8622,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8621])).

cnf(c_8630,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8622])).

cnf(c_8666,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8630,c_41])).

cnf(c_8667,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8666])).

cnf(c_8675,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8667])).

cnf(c_8728,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8675,c_41])).

cnf(c_8729,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8728])).

cnf(c_8737,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8729])).

cnf(c_10115,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8737,c_41])).

cnf(c_10116,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10115])).

cnf(c_10124,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_10116])).

cnf(c_12834,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10124,c_41])).

cnf(c_12835,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12834])).

cnf(c_12843,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_12835])).

cnf(c_14215,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12843,c_41])).

cnf(c_14216,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14215])).

cnf(c_14224,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_14216])).

cnf(c_16243,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14224,c_41])).

cnf(c_16244,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_16243])).

cnf(c_16252,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_16244])).

cnf(c_17019,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16252,c_41])).

cnf(c_17020,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_17019])).

cnf(c_17028,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_17020])).

cnf(c_19199,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17028,c_41])).

cnf(c_19200,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_19199])).

cnf(c_19208,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_19200])).

cnf(c_20550,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19208,c_41])).

cnf(c_20551,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_20550])).

cnf(c_20559,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_20551])).

cnf(c_23136,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20559,c_41])).

cnf(c_23137,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_23136])).

cnf(c_23145,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_23137])).

cnf(c_24446,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23145,c_41])).

cnf(c_24447,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_24446])).

cnf(c_24455,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_24447])).

cnf(c_27016,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24455,c_41])).

cnf(c_27017,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_27016])).

cnf(c_27025,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_27017])).

cnf(c_28299,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27025,c_41])).

cnf(c_28300,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_28299])).

cnf(c_28308,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_28300])).

cnf(c_31978,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28308,c_41])).

cnf(c_31979,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_31978])).

cnf(c_31987,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_31979])).

cnf(c_33457,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31987,c_41])).

cnf(c_33458,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_33457])).

cnf(c_33466,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_33458])).

cnf(c_37051,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33466,c_41])).

cnf(c_37052,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37051])).

cnf(c_37060,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_37052])).

cnf(c_37902,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37060,c_41])).

cnf(c_37903,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_37902])).

cnf(c_37911,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_37903])).

cnf(c_40297,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37911,c_41])).

cnf(c_40298,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_40297])).

cnf(c_40306,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_40298])).

cnf(c_41141,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_40306,c_41])).

cnf(c_41142,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_41141])).

cnf(c_41150,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_41142])).

cnf(c_43809,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41150,c_41])).

cnf(c_43810,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_43809])).

cnf(c_43818,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_43810])).

cnf(c_44954,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_43818,c_41])).

cnf(c_44955,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_44954])).

cnf(c_44963,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_44955])).

cnf(c_47909,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44963,c_41])).

cnf(c_47910,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_47909])).

cnf(c_47918,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_47910])).

cnf(c_49784,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47918,c_41])).

cnf(c_49785,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_49784])).

cnf(c_49793,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_49785])).

cnf(c_54555,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_49793,c_41])).

cnf(c_54556,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_54555])).

cnf(c_54564,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_54556])).

cnf(c_56397,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54564,c_41])).

cnf(c_56398,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_56397])).

cnf(c_56406,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_56398])).

cnf(c_60109,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56406,c_41])).

cnf(c_60110,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_60109])).

cnf(c_60118,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_60110])).

cnf(c_61038,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60118,c_41])).

cnf(c_61039,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_61038])).

cnf(c_61047,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_61039])).

cnf(c_64084,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61047,c_41])).

cnf(c_64085,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_64084])).

cnf(c_64093,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_64085])).

cnf(c_65147,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64093,c_41])).

cnf(c_65148,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_65147])).

cnf(c_65156,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_65148])).

cnf(c_68608,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_65156,c_41])).

cnf(c_68609,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_68608])).

cnf(c_68617,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_68609])).

cnf(c_69904,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_68617,c_41])).

cnf(c_69905,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_69904])).

cnf(c_69913,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_69905])).

cnf(c_73883,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_69913,c_41])).

cnf(c_73884,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_73883])).

cnf(c_73892,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_73884])).

cnf(c_75440,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73892,c_41])).

cnf(c_75441,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_75440])).

cnf(c_75449,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_75441])).

cnf(c_79397,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_75449,c_41])).

cnf(c_79398,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_79397])).

cnf(c_79406,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_79398])).

cnf(c_80720,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79406,c_41])).

cnf(c_80721,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_80720])).

cnf(c_80729,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_80721])).

cnf(c_84299,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_80729,c_41])).

cnf(c_84300,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_84299])).

cnf(c_84308,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_84300])).

cnf(c_85847,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_84308,c_41])).

cnf(c_85848,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_85847])).

cnf(c_85856,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_85848])).

cnf(c_90018,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_85856,c_41])).

cnf(c_90019,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_90018])).

cnf(c_90027,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_90019])).

cnf(c_92151,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_90027,c_41])).

cnf(c_92152,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_92151])).

cnf(c_92160,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_92152])).

cnf(c_96029,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_92160,c_41])).

cnf(c_96030,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_96029])).

cnf(c_96039,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))))))))))))))))))))))))))))))))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_96030])).

cnf(c_1576,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1605,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_765,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_37])).

cnf(c_766,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_770,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_766,c_36,c_35])).

cnf(c_771,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_770])).

cnf(c_1113,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | v5_pre_topc(X0,X1,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_771,c_39])).

cnf(c_1114,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1113])).

cnf(c_1118,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_38])).

cnf(c_1119,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0,sK2,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1118])).

cnf(c_1540,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | v5_pre_topc(X0_55,sK2,sK3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X0_55))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1119])).

cnf(c_1687,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(X0_55,sK2,sK3) = iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X0_55)))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1540])).

cnf(c_1689,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1571,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57)
    | ~ v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2995,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)),X0_57,sK3)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55))
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_2996,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)),X0_57,sK3) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2995])).

cnf(c_2998,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2996])).

cnf(c_3002,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3008,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3002])).

cnf(c_3001,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_3010,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3001])).

cnf(c_3000,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
    inference(instantiation,[status(thm)],[c_1566])).

cnf(c_3012,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3000])).

cnf(c_4562,plain,
    ( sK0(sK2,sK3,X0_55) = sK0(sK2,sK3,X0_55) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_4564,plain,
    ( sK0(sK2,sK3,sK4) = sK0(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_4562])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1562,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
    | k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k7_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2336,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
    | k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k7_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_3928,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3921,c_2336])).

cnf(c_5063,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3928,c_41,c_44,c_45,c_46,c_47,c_50,c_130,c_2900,c_3328])).

cnf(c_5064,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5063])).

cnf(c_5073,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_5064])).

cnf(c_5072,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_5064])).

cnf(c_5603,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5072,c_41])).

cnf(c_5604,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5603])).

cnf(c_5613,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_5604])).

cnf(c_8419,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_8410])).

cnf(c_8464,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_8455])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_696,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_37])).

cnf(c_697,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_701,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_36,c_35])).

cnf(c_702,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_701])).

cnf(c_1167,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,X1,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_39])).

cnf(c_1168,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1167])).

cnf(c_1172,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1168,c_38])).

cnf(c_1173,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0,sK2,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_1172])).

cnf(c_1538,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0_55,sK2,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,X1_55)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55)))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_1173])).

cnf(c_3477,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(X0_55,sK2,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X1_55))))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_8560,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK2,sK3)
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))))
    | ~ m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55))) ),
    inference(instantiation,[status(thm)],[c_3477])).

cnf(c_8573,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK2,sK3) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)))) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8560])).

cnf(c_8575,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8573])).

cnf(c_2,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v5_pre_topc(X0_55,X0_57,X1_57)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57)
    | v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2326,plain,
    ( k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X0_57)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | v5_pre_topc(X0_55,X0_57,X1_57) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57) != iProver_top
    | v3_tops_2(X0_55,X0_57,X1_57) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_4606,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4600,c_2326])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_606,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_37])).

cnf(c_607,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v3_tops_2(X0,X1,sK3)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
    | ~ v3_tops_2(X0,X1,sK3)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_35])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ v3_tops_2(X0,X1,sK3)
    | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_1549,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
    | ~ v3_tops_2(X0_55,X0_57,sK3)
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_1660,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(X0_55,X0_57,sK3) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_1662,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_636,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_37])).

cnf(c_637,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK3)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_1548,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK3)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_637])).

cnf(c_1663,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v2_funct_1(X0_55) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_1665,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_522,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_37])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_527,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_36,c_35])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_527])).

cnf(c_1233,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_528,c_39])).

cnf(c_1234,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_1238,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v3_tops_2(X0,sK3,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_38])).

cnf(c_1239,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1238])).

cnf(c_1536,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0_55,sK3,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | m1_subset_1(sK1(sK3,sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1239])).

cnf(c_3079,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_3080,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3079])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_564,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)))
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_37])).

cnf(c_565,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_569,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_565,c_36,c_35])).

cnf(c_570,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_569])).

cnf(c_1197,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_570,c_39])).

cnf(c_1198,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1197])).

cnf(c_1202,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v3_tops_2(X0,sK3,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_38])).

cnf(c_1203,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1202])).

cnf(c_1537,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(X0_55,sK3,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK2)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,sK1(sK3,sK2,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,sK1(sK3,sK2,X0_55))) ),
    inference(subtyping,[status(esa)],[c_1203])).

cnf(c_3082,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_3083,plain,
    ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3082])).

cnf(c_28,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1558,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3151,plain,
    ( v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_3152,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3151])).

cnf(c_3164,plain,
    ( ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_3165,plain,
    ( m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3164])).

cnf(c_3159,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57))))
    | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55) != k2_struct_0(X0_57)
    | k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_3599,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_3159])).

cnf(c_3600,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3599])).

cnf(c_1578,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_3452,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_3779,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_3452])).

cnf(c_3780,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_3552,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57))))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55)
    | ~ v2_funct_1(X0_55)
    | ~ l1_struct_0(X0_57)
    | ~ l1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55) != k2_struct_0(X0_57)
    | k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_4031,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_3552])).

cnf(c_4032,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4031])).

cnf(c_3781,plain,
    ( X0_55 != X1_55
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X1_55
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = X0_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_4518,plain,
    ( X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = X0_55
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_3781])).

cnf(c_4800,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_4518])).

cnf(c_4486,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_5918,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_4486])).

cnf(c_1580,plain,
    ( X0_55 != X1_55
    | k2_pre_topc(X0_57,X0_55) = k2_pre_topc(X0_57,X1_55) ),
    theory(equality)).

cnf(c_5939,plain,
    ( X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_pre_topc(sK3,X0_55) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_6180,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
    | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
    inference(instantiation,[status(thm)],[c_5939])).

cnf(c_9944,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4606,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_5918,c_6180])).

cnf(c_7049,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_36987,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_7049])).

cnf(c_36989,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_36987])).

cnf(c_1589,plain,
    ( X0_55 != X1_55
    | X2_55 != X3_55
    | k7_relset_1(X0_56,X1_56,X0_55,X2_55) = k7_relset_1(X0_56,X1_56,X1_55,X3_55) ),
    theory(equality)).

cnf(c_7055,plain,
    ( X0_55 != X1_55
    | X2_55 != X3_55
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X2_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X1_55,X3_55) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_37643,plain,
    ( X0_55 != sK0(sK2,sK3,X1_55)
    | X2_55 != sK4
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2_55,X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55)) ),
    inference(instantiation,[status(thm)],[c_7055])).

cnf(c_44951,plain,
    ( X0_55 != sK4
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X1_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55))
    | sK0(sK2,sK3,X1_55) != sK0(sK2,sK3,X1_55) ),
    inference(instantiation,[status(thm)],[c_37643])).

cnf(c_44952,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
    | sK0(sK2,sK3,sK4) != sK0(sK2,sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_44951])).

cnf(c_63383,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)) != X2_55
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))) = k2_pre_topc(sK3,X2_55) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_64850,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK0(sK2,sK3,X1_55))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK0(sK2,sK3,X1_55))) ),
    inference(instantiation,[status(thm)],[c_63383])).

cnf(c_64851,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_64850])).

cnf(c_64646,plain,
    ( X0_55 != X1_55
    | X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))) != X1_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_67930,plain,
    ( X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55)))
    | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))) ),
    inference(instantiation,[status(thm)],[c_64646])).

cnf(c_69832,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_67930])).

cnf(c_69834,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_69832])).

cnf(c_66745,plain,
    ( X0_55 != X1_55
    | X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),sK0(sK2,sK3,X3_55))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),sK0(sK2,sK3,X3_55)) != X1_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_68340,plain,
    ( X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X1_55))
    | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X1_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55)) ),
    inference(instantiation,[status(thm)],[c_66745])).

cnf(c_69960,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) ),
    inference(instantiation,[status(thm)],[c_68340])).

cnf(c_69962,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_69960])).

cnf(c_62242,plain,
    ( X0_55 != X1_55
    | X0_55 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))) != X1_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_63371,plain,
    ( X0_55 != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
    | X0_55 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))) ),
    inference(instantiation,[status(thm)],[c_62242])).

cnf(c_75126,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_63371])).

cnf(c_75127,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_75126])).

cnf(c_68567,plain,
    ( X0_55 != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))
    | k2_pre_topc(sK3,X0_55) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_75360,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_68567])).

cnf(c_75365,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_75360])).

cnf(c_62785,plain,
    ( X0_55 != X1_55
    | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) != X1_55 ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_63382,plain,
    ( X0_55 != k2_pre_topc(sK3,X1_55)
    | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) != k2_pre_topc(sK3,X1_55) ),
    inference(instantiation,[status(thm)],[c_62785])).

cnf(c_66741,plain,
    ( X0_55 != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55)))
    | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),sK0(sK2,sK3,X2_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),sK0(sK2,sK3,X2_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))) ),
    inference(instantiation,[status(thm)],[c_63382])).

cnf(c_85839,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_66741])).

cnf(c_85841,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_85839])).

cnf(c_1590,plain,
    ( ~ r1_tarski(X0_55,X1_55)
    | r1_tarski(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_61114,plain,
    ( r1_tarski(X0_55,X1_55)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))))
    | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
    | X1_55 != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_62244,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55),X2_55)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X4_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),sK0(sK2,sK3,X4_55))))
    | X2_55 != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),sK0(sK2,sK3,X4_55)))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X4_55))) ),
    inference(instantiation,[status(thm)],[c_61114])).

cnf(c_84611,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X2_55))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X2_55))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X2_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X2_55))) ),
    inference(instantiation,[status(thm)],[c_62244])).

cnf(c_95822,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) ),
    inference(instantiation,[status(thm)],[c_84611])).

cnf(c_95823,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_95822])).

cnf(c_95825,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95823])).

cnf(c_96447,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96039,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1605,c_1556,c_1662,c_1665,c_1689,c_2900,c_2937,c_2940,c_2943,c_2998,c_3008,c_3010,c_3012,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4132,c_4564,c_4800,c_5073,c_5613,c_5918,c_6180,c_8419,c_8464,c_8575,c_36989,c_44952,c_64851,c_69834,c_69962,c_75127,c_75365,c_85841,c_95825])).

cnf(c_2340,plain,
    ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_3060,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_2340])).

cnf(c_4251,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3060,c_41])).

cnf(c_4252,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4251])).

cnf(c_4260,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4252])).

cnf(c_4281,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4260,c_41])).

cnf(c_4282,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4281])).

cnf(c_4290,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4282])).

cnf(c_4381,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4290,c_41])).

cnf(c_4382,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4381])).

cnf(c_4390,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4382])).

cnf(c_4829,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4390,c_41])).

cnf(c_4830,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4829])).

cnf(c_4839,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4830])).

cnf(c_4860,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4839,c_41])).

cnf(c_4861,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4860])).

cnf(c_4870,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4861])).

cnf(c_4919,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4870,c_41])).

cnf(c_4920,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4919])).

cnf(c_4930,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_4920])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1570,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | v5_pre_topc(X0_55,X0_57,X1_57)
    | ~ v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2956,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55))
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_2957,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2956])).

cnf(c_2959,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_3930,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3921,c_2326])).

cnf(c_31,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1555,negated_conjecture,
    ( v3_tops_2(sK4,sK2,sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2343,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1555])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v3_tops_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1567,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ v3_tops_2(X0_55,X0_57,X1_57)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_55)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2961,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tops_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_3023,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2343,c_38,c_35,c_34,c_33,c_32,c_1555,c_2961])).

cnf(c_3941,plain,
    ( k2_struct_0(sK2) != k2_struct_0(sK2)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3930,c_3023])).

cnf(c_3942,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3941])).

cnf(c_4950,plain,
    ( v3_tops_2(sK4,sK2,sK3) = iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3942,c_41,c_44,c_45,c_46,c_47,c_50,c_3328])).

cnf(c_4951,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4950])).

cnf(c_6599,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4930,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_4951,c_5918,c_6180])).

cnf(c_27,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1559,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2339,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_3027,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_struct_0(sK2) != k2_struct_0(sK2)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3023,c_2339])).

cnf(c_3028,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3027])).

cnf(c_1648,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_3413,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_3234,plain,
    ( X0_59 != X1_59
    | k2_struct_0(sK3) != X1_59
    | k2_struct_0(sK3) = X0_59 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_3412,plain,
    ( X0_59 != k2_struct_0(sK3)
    | k2_struct_0(sK3) = X0_59
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3234])).

cnf(c_3608,plain,
    ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3412])).

cnf(c_3609,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_4542,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3028,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_50,c_1648,c_1556,c_1555,c_2961,c_3232,c_3252,c_3328,c_3413,c_3609,c_3754])).

cnf(c_4543,plain,
    ( v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4542])).

cnf(c_5611,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5604])).

cnf(c_8202,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) ),
    inference(superposition,[status(thm)],[c_6599,c_5611])).

cnf(c_2360,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(X0_55,sK2,sK3) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,X1_55)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55))) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_56160,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8202,c_2360])).

cnf(c_56870,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56160,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_4951,c_5611,c_5918,c_6180])).

cnf(c_96457,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_96447,c_56870])).

cnf(c_5071,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5064])).

cnf(c_8183,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) ),
    inference(superposition,[status(thm)],[c_6599,c_5071])).

cnf(c_49465,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8183,c_2360])).

cnf(c_50081,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49465,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_4951,c_5071,c_5918,c_6180])).

cnf(c_96458,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_96447,c_50081])).

cnf(c_4840,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_4830])).

cnf(c_6416,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))
    | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4840,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_4951,c_5918,c_6180])).

cnf(c_2349,plain,
    ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(X0_55,X0_57,sK3) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_2332,plain,
    ( v1_funct_2(X0_55,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_486,plain,
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
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_37])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_36,c_35])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_1269,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ v3_tops_2(X0,sK3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_39])).

cnf(c_1270,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
    inference(unflattening,[status(thm)],[c_1269])).

cnf(c_1274,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v3_tops_2(X0,sK3,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_38])).

cnf(c_1275,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v3_tops_2(X0,sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
    inference(renaming,[status(thm)],[c_1274])).

cnf(c_1535,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v3_tops_2(X0_55,sK3,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_funct_1(X0_55)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_1275])).

cnf(c_2363,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(X0_55,sK3,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_3463,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2332,c_2363])).

cnf(c_3069,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_3073,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3069])).

cnf(c_3068,plain,
    ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(X0_55) ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_3075,plain,
    ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3068])).

cnf(c_5251,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3463,c_3073,c_3075])).

cnf(c_5252,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_5251])).

cnf(c_5263,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(X0_55,sK2,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2349,c_5252])).

cnf(c_5349,plain,
    ( v1_funct_1(X0_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v3_tops_2(X0_55,sK2,sK3) != iProver_top
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5263,c_41,c_2883,c_3073,c_3075,c_3463])).

cnf(c_5350,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
    | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(X0_55,sK2,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_5349])).

cnf(c_5361,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2344,c_5350])).

cnf(c_5396,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5361,c_45,c_46])).

cnf(c_5397,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5396])).

cnf(c_5405,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4543,c_5397])).

cnf(c_6422,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) ),
    inference(superposition,[status(thm)],[c_6416,c_5405])).

cnf(c_15168,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_2360])).

cnf(c_15945,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
    | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15168,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,c_4800,c_4951,c_5405,c_5918,c_6180])).

cnf(c_96459,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_96447,c_15945])).

cnf(c_96463,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_96458,c_96459])).

cnf(c_96467,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_96457,c_96463])).

cnf(c_26,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1560,negated_conjecture,
    ( ~ v3_tops_2(sK4,sK2,sK3)
    | ~ v2_funct_1(sK4)
    | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2338,plain,
    ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
    | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
    | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_3026,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k2_struct_0(sK2) != k2_struct_0(sK2)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3023,c_2338])).

cnf(c_3037,plain,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
    | v3_tops_2(sK4,sK2,sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3026])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_96467,c_96447,c_9944,c_4951,c_3921,c_3426,c_3037,c_2959,c_2943,c_2940,c_2937,c_47,c_46,c_45,c_44,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 48.04/6.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.04/6.49  
% 48.04/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 48.04/6.49  
% 48.04/6.49  ------  iProver source info
% 48.04/6.49  
% 48.04/6.49  git: date: 2020-06-30 10:37:57 +0100
% 48.04/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 48.04/6.49  git: non_committed_changes: false
% 48.04/6.49  git: last_make_outside_of_git: false
% 48.04/6.49  
% 48.04/6.49  ------ 
% 48.04/6.49  
% 48.04/6.49  ------ Input Options
% 48.04/6.49  
% 48.04/6.49  --out_options                           all
% 48.04/6.49  --tptp_safe_out                         true
% 48.04/6.49  --problem_path                          ""
% 48.04/6.49  --include_path                          ""
% 48.04/6.49  --clausifier                            res/vclausify_rel
% 48.04/6.49  --clausifier_options                    --mode clausify
% 48.04/6.49  --stdin                                 false
% 48.04/6.49  --stats_out                             all
% 48.04/6.49  
% 48.04/6.49  ------ General Options
% 48.04/6.49  
% 48.04/6.49  --fof                                   false
% 48.04/6.49  --time_out_real                         305.
% 48.04/6.49  --time_out_virtual                      -1.
% 48.04/6.49  --symbol_type_check                     false
% 48.04/6.49  --clausify_out                          false
% 48.04/6.49  --sig_cnt_out                           false
% 48.04/6.49  --trig_cnt_out                          false
% 48.04/6.49  --trig_cnt_out_tolerance                1.
% 48.04/6.49  --trig_cnt_out_sk_spl                   false
% 48.04/6.49  --abstr_cl_out                          false
% 48.04/6.49  
% 48.04/6.49  ------ Global Options
% 48.04/6.49  
% 48.04/6.49  --schedule                              default
% 48.04/6.49  --add_important_lit                     false
% 48.04/6.49  --prop_solver_per_cl                    1000
% 48.04/6.49  --min_unsat_core                        false
% 48.04/6.49  --soft_assumptions                      false
% 48.04/6.49  --soft_lemma_size                       3
% 48.04/6.49  --prop_impl_unit_size                   0
% 48.04/6.49  --prop_impl_unit                        []
% 48.04/6.49  --share_sel_clauses                     true
% 48.04/6.49  --reset_solvers                         false
% 48.04/6.49  --bc_imp_inh                            [conj_cone]
% 48.04/6.49  --conj_cone_tolerance                   3.
% 48.04/6.49  --extra_neg_conj                        none
% 48.04/6.49  --large_theory_mode                     true
% 48.04/6.49  --prolific_symb_bound                   200
% 48.04/6.49  --lt_threshold                          2000
% 48.04/6.49  --clause_weak_htbl                      true
% 48.04/6.49  --gc_record_bc_elim                     false
% 48.04/6.49  
% 48.04/6.49  ------ Preprocessing Options
% 48.04/6.49  
% 48.04/6.49  --preprocessing_flag                    true
% 48.04/6.49  --time_out_prep_mult                    0.1
% 48.04/6.49  --splitting_mode                        input
% 48.04/6.49  --splitting_grd                         true
% 48.04/6.49  --splitting_cvd                         false
% 48.04/6.49  --splitting_cvd_svl                     false
% 48.04/6.49  --splitting_nvd                         32
% 48.04/6.49  --sub_typing                            true
% 48.04/6.49  --prep_gs_sim                           true
% 48.04/6.49  --prep_unflatten                        true
% 48.04/6.49  --prep_res_sim                          true
% 48.04/6.49  --prep_upred                            true
% 48.04/6.49  --prep_sem_filter                       exhaustive
% 48.04/6.49  --prep_sem_filter_out                   false
% 48.04/6.49  --pred_elim                             true
% 48.04/6.49  --res_sim_input                         true
% 48.04/6.49  --eq_ax_congr_red                       true
% 48.04/6.49  --pure_diseq_elim                       true
% 48.04/6.49  --brand_transform                       false
% 48.04/6.49  --non_eq_to_eq                          false
% 48.04/6.49  --prep_def_merge                        true
% 48.04/6.49  --prep_def_merge_prop_impl              false
% 48.04/6.49  --prep_def_merge_mbd                    true
% 48.04/6.49  --prep_def_merge_tr_red                 false
% 48.04/6.49  --prep_def_merge_tr_cl                  false
% 48.04/6.49  --smt_preprocessing                     true
% 48.04/6.49  --smt_ac_axioms                         fast
% 48.04/6.49  --preprocessed_out                      false
% 48.04/6.49  --preprocessed_stats                    false
% 48.04/6.49  
% 48.04/6.49  ------ Abstraction refinement Options
% 48.04/6.49  
% 48.04/6.49  --abstr_ref                             []
% 48.04/6.49  --abstr_ref_prep                        false
% 48.04/6.49  --abstr_ref_until_sat                   false
% 48.04/6.49  --abstr_ref_sig_restrict                funpre
% 48.04/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 48.04/6.49  --abstr_ref_under                       []
% 48.04/6.49  
% 48.04/6.49  ------ SAT Options
% 48.04/6.49  
% 48.04/6.49  --sat_mode                              false
% 48.04/6.49  --sat_fm_restart_options                ""
% 48.04/6.49  --sat_gr_def                            false
% 48.04/6.49  --sat_epr_types                         true
% 48.04/6.49  --sat_non_cyclic_types                  false
% 48.04/6.49  --sat_finite_models                     false
% 48.04/6.49  --sat_fm_lemmas                         false
% 48.04/6.49  --sat_fm_prep                           false
% 48.04/6.49  --sat_fm_uc_incr                        true
% 48.04/6.49  --sat_out_model                         small
% 48.04/6.49  --sat_out_clauses                       false
% 48.04/6.49  
% 48.04/6.49  ------ QBF Options
% 48.04/6.49  
% 48.04/6.49  --qbf_mode                              false
% 48.04/6.49  --qbf_elim_univ                         false
% 48.04/6.49  --qbf_dom_inst                          none
% 48.04/6.49  --qbf_dom_pre_inst                      false
% 48.04/6.49  --qbf_sk_in                             false
% 48.04/6.49  --qbf_pred_elim                         true
% 48.04/6.49  --qbf_split                             512
% 48.04/6.49  
% 48.04/6.49  ------ BMC1 Options
% 48.04/6.49  
% 48.04/6.49  --bmc1_incremental                      false
% 48.04/6.49  --bmc1_axioms                           reachable_all
% 48.04/6.49  --bmc1_min_bound                        0
% 48.04/6.49  --bmc1_max_bound                        -1
% 48.04/6.49  --bmc1_max_bound_default                -1
% 48.04/6.49  --bmc1_symbol_reachability              true
% 48.04/6.49  --bmc1_property_lemmas                  false
% 48.04/6.49  --bmc1_k_induction                      false
% 48.04/6.49  --bmc1_non_equiv_states                 false
% 48.04/6.49  --bmc1_deadlock                         false
% 48.04/6.49  --bmc1_ucm                              false
% 48.04/6.49  --bmc1_add_unsat_core                   none
% 48.04/6.49  --bmc1_unsat_core_children              false
% 48.04/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 48.04/6.49  --bmc1_out_stat                         full
% 48.04/6.49  --bmc1_ground_init                      false
% 48.04/6.49  --bmc1_pre_inst_next_state              false
% 48.04/6.49  --bmc1_pre_inst_state                   false
% 48.04/6.49  --bmc1_pre_inst_reach_state             false
% 48.04/6.49  --bmc1_out_unsat_core                   false
% 48.04/6.49  --bmc1_aig_witness_out                  false
% 48.04/6.49  --bmc1_verbose                          false
% 48.04/6.49  --bmc1_dump_clauses_tptp                false
% 48.04/6.49  --bmc1_dump_unsat_core_tptp             false
% 48.04/6.49  --bmc1_dump_file                        -
% 48.04/6.49  --bmc1_ucm_expand_uc_limit              128
% 48.04/6.49  --bmc1_ucm_n_expand_iterations          6
% 48.04/6.49  --bmc1_ucm_extend_mode                  1
% 48.04/6.49  --bmc1_ucm_init_mode                    2
% 48.04/6.49  --bmc1_ucm_cone_mode                    none
% 48.04/6.49  --bmc1_ucm_reduced_relation_type        0
% 48.04/6.49  --bmc1_ucm_relax_model                  4
% 48.04/6.49  --bmc1_ucm_full_tr_after_sat            true
% 48.04/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 48.04/6.49  --bmc1_ucm_layered_model                none
% 48.04/6.49  --bmc1_ucm_max_lemma_size               10
% 48.04/6.49  
% 48.04/6.49  ------ AIG Options
% 48.04/6.49  
% 48.04/6.49  --aig_mode                              false
% 48.04/6.49  
% 48.04/6.49  ------ Instantiation Options
% 48.04/6.49  
% 48.04/6.49  --instantiation_flag                    true
% 48.04/6.49  --inst_sos_flag                         false
% 48.04/6.49  --inst_sos_phase                        true
% 48.04/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 48.04/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 48.04/6.49  --inst_lit_sel_side                     num_symb
% 48.04/6.49  --inst_solver_per_active                1400
% 48.04/6.49  --inst_solver_calls_frac                1.
% 48.04/6.49  --inst_passive_queue_type               priority_queues
% 48.04/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 48.04/6.49  --inst_passive_queues_freq              [25;2]
% 48.04/6.49  --inst_dismatching                      true
% 48.04/6.49  --inst_eager_unprocessed_to_passive     true
% 48.04/6.49  --inst_prop_sim_given                   true
% 48.04/6.49  --inst_prop_sim_new                     false
% 48.04/6.49  --inst_subs_new                         false
% 48.04/6.49  --inst_eq_res_simp                      false
% 48.04/6.49  --inst_subs_given                       false
% 48.04/6.49  --inst_orphan_elimination               true
% 48.04/6.49  --inst_learning_loop_flag               true
% 48.04/6.49  --inst_learning_start                   3000
% 48.04/6.49  --inst_learning_factor                  2
% 48.04/6.49  --inst_start_prop_sim_after_learn       3
% 48.04/6.49  --inst_sel_renew                        solver
% 48.04/6.49  --inst_lit_activity_flag                true
% 48.04/6.49  --inst_restr_to_given                   false
% 48.04/6.49  --inst_activity_threshold               500
% 48.04/6.49  --inst_out_proof                        true
% 48.04/6.49  
% 48.04/6.49  ------ Resolution Options
% 48.04/6.49  
% 48.04/6.49  --resolution_flag                       true
% 48.04/6.49  --res_lit_sel                           adaptive
% 48.04/6.49  --res_lit_sel_side                      none
% 48.04/6.49  --res_ordering                          kbo
% 48.04/6.49  --res_to_prop_solver                    active
% 48.04/6.49  --res_prop_simpl_new                    false
% 48.04/6.49  --res_prop_simpl_given                  true
% 48.04/6.49  --res_passive_queue_type                priority_queues
% 48.04/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 48.04/6.49  --res_passive_queues_freq               [15;5]
% 48.04/6.49  --res_forward_subs                      full
% 48.04/6.49  --res_backward_subs                     full
% 48.04/6.49  --res_forward_subs_resolution           true
% 48.04/6.49  --res_backward_subs_resolution          true
% 48.04/6.49  --res_orphan_elimination                true
% 48.04/6.49  --res_time_limit                        2.
% 48.04/6.49  --res_out_proof                         true
% 48.04/6.49  
% 48.04/6.49  ------ Superposition Options
% 48.04/6.49  
% 48.04/6.49  --superposition_flag                    true
% 48.04/6.49  --sup_passive_queue_type                priority_queues
% 48.04/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 48.04/6.49  --sup_passive_queues_freq               [8;1;4]
% 48.04/6.49  --demod_completeness_check              fast
% 48.04/6.49  --demod_use_ground                      true
% 48.04/6.49  --sup_to_prop_solver                    passive
% 48.04/6.49  --sup_prop_simpl_new                    true
% 48.04/6.49  --sup_prop_simpl_given                  true
% 48.04/6.49  --sup_fun_splitting                     false
% 48.04/6.49  --sup_smt_interval                      50000
% 48.04/6.49  
% 48.04/6.49  ------ Superposition Simplification Setup
% 48.04/6.49  
% 48.04/6.49  --sup_indices_passive                   []
% 48.04/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 48.04/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_full_bw                           [BwDemod]
% 48.04/6.49  --sup_immed_triv                        [TrivRules]
% 48.04/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 48.04/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_immed_bw_main                     []
% 48.04/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 48.04/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 48.04/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 48.04/6.49  
% 48.04/6.49  ------ Combination Options
% 48.04/6.49  
% 48.04/6.49  --comb_res_mult                         3
% 48.04/6.49  --comb_sup_mult                         2
% 48.04/6.49  --comb_inst_mult                        10
% 48.04/6.49  
% 48.04/6.49  ------ Debug Options
% 48.04/6.49  
% 48.04/6.49  --dbg_backtrace                         false
% 48.04/6.49  --dbg_dump_prop_clauses                 false
% 48.04/6.49  --dbg_dump_prop_clauses_file            -
% 48.04/6.49  --dbg_out_stat                          false
% 48.04/6.49  ------ Parsing...
% 48.04/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 48.04/6.49  
% 48.04/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 48.04/6.49  
% 48.04/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 48.04/6.49  
% 48.04/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 48.04/6.49  ------ Proving...
% 48.04/6.49  ------ Problem Properties 
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  clauses                                 40
% 48.04/6.49  conjectures                             11
% 48.04/6.49  EPR                                     5
% 48.04/6.49  Horn                                    32
% 48.04/6.49  unary                                   5
% 48.04/6.49  binary                                  4
% 48.04/6.49  lits                                    211
% 48.04/6.49  lits eq                                 33
% 48.04/6.49  fd_pure                                 0
% 48.04/6.49  fd_pseudo                               0
% 48.04/6.49  fd_cond                                 0
% 48.04/6.49  fd_pseudo_cond                          0
% 48.04/6.49  AC symbols                              0
% 48.04/6.49  
% 48.04/6.49  ------ Schedule dynamic 5 is on 
% 48.04/6.49  
% 48.04/6.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  ------ 
% 48.04/6.49  Current options:
% 48.04/6.49  ------ 
% 48.04/6.49  
% 48.04/6.49  ------ Input Options
% 48.04/6.49  
% 48.04/6.49  --out_options                           all
% 48.04/6.49  --tptp_safe_out                         true
% 48.04/6.49  --problem_path                          ""
% 48.04/6.49  --include_path                          ""
% 48.04/6.49  --clausifier                            res/vclausify_rel
% 48.04/6.49  --clausifier_options                    --mode clausify
% 48.04/6.49  --stdin                                 false
% 48.04/6.49  --stats_out                             all
% 48.04/6.49  
% 48.04/6.49  ------ General Options
% 48.04/6.49  
% 48.04/6.49  --fof                                   false
% 48.04/6.49  --time_out_real                         305.
% 48.04/6.49  --time_out_virtual                      -1.
% 48.04/6.49  --symbol_type_check                     false
% 48.04/6.49  --clausify_out                          false
% 48.04/6.49  --sig_cnt_out                           false
% 48.04/6.49  --trig_cnt_out                          false
% 48.04/6.49  --trig_cnt_out_tolerance                1.
% 48.04/6.49  --trig_cnt_out_sk_spl                   false
% 48.04/6.49  --abstr_cl_out                          false
% 48.04/6.49  
% 48.04/6.49  ------ Global Options
% 48.04/6.49  
% 48.04/6.49  --schedule                              default
% 48.04/6.49  --add_important_lit                     false
% 48.04/6.49  --prop_solver_per_cl                    1000
% 48.04/6.49  --min_unsat_core                        false
% 48.04/6.49  --soft_assumptions                      false
% 48.04/6.49  --soft_lemma_size                       3
% 48.04/6.49  --prop_impl_unit_size                   0
% 48.04/6.49  --prop_impl_unit                        []
% 48.04/6.49  --share_sel_clauses                     true
% 48.04/6.49  --reset_solvers                         false
% 48.04/6.49  --bc_imp_inh                            [conj_cone]
% 48.04/6.49  --conj_cone_tolerance                   3.
% 48.04/6.49  --extra_neg_conj                        none
% 48.04/6.49  --large_theory_mode                     true
% 48.04/6.49  --prolific_symb_bound                   200
% 48.04/6.49  --lt_threshold                          2000
% 48.04/6.49  --clause_weak_htbl                      true
% 48.04/6.49  --gc_record_bc_elim                     false
% 48.04/6.49  
% 48.04/6.49  ------ Preprocessing Options
% 48.04/6.49  
% 48.04/6.49  --preprocessing_flag                    true
% 48.04/6.49  --time_out_prep_mult                    0.1
% 48.04/6.49  --splitting_mode                        input
% 48.04/6.49  --splitting_grd                         true
% 48.04/6.49  --splitting_cvd                         false
% 48.04/6.49  --splitting_cvd_svl                     false
% 48.04/6.49  --splitting_nvd                         32
% 48.04/6.49  --sub_typing                            true
% 48.04/6.49  --prep_gs_sim                           true
% 48.04/6.49  --prep_unflatten                        true
% 48.04/6.49  --prep_res_sim                          true
% 48.04/6.49  --prep_upred                            true
% 48.04/6.49  --prep_sem_filter                       exhaustive
% 48.04/6.49  --prep_sem_filter_out                   false
% 48.04/6.49  --pred_elim                             true
% 48.04/6.49  --res_sim_input                         true
% 48.04/6.49  --eq_ax_congr_red                       true
% 48.04/6.49  --pure_diseq_elim                       true
% 48.04/6.49  --brand_transform                       false
% 48.04/6.49  --non_eq_to_eq                          false
% 48.04/6.49  --prep_def_merge                        true
% 48.04/6.49  --prep_def_merge_prop_impl              false
% 48.04/6.49  --prep_def_merge_mbd                    true
% 48.04/6.49  --prep_def_merge_tr_red                 false
% 48.04/6.49  --prep_def_merge_tr_cl                  false
% 48.04/6.49  --smt_preprocessing                     true
% 48.04/6.49  --smt_ac_axioms                         fast
% 48.04/6.49  --preprocessed_out                      false
% 48.04/6.49  --preprocessed_stats                    false
% 48.04/6.49  
% 48.04/6.49  ------ Abstraction refinement Options
% 48.04/6.49  
% 48.04/6.49  --abstr_ref                             []
% 48.04/6.49  --abstr_ref_prep                        false
% 48.04/6.49  --abstr_ref_until_sat                   false
% 48.04/6.49  --abstr_ref_sig_restrict                funpre
% 48.04/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 48.04/6.49  --abstr_ref_under                       []
% 48.04/6.49  
% 48.04/6.49  ------ SAT Options
% 48.04/6.49  
% 48.04/6.49  --sat_mode                              false
% 48.04/6.49  --sat_fm_restart_options                ""
% 48.04/6.49  --sat_gr_def                            false
% 48.04/6.49  --sat_epr_types                         true
% 48.04/6.49  --sat_non_cyclic_types                  false
% 48.04/6.49  --sat_finite_models                     false
% 48.04/6.49  --sat_fm_lemmas                         false
% 48.04/6.49  --sat_fm_prep                           false
% 48.04/6.49  --sat_fm_uc_incr                        true
% 48.04/6.49  --sat_out_model                         small
% 48.04/6.49  --sat_out_clauses                       false
% 48.04/6.49  
% 48.04/6.49  ------ QBF Options
% 48.04/6.49  
% 48.04/6.49  --qbf_mode                              false
% 48.04/6.49  --qbf_elim_univ                         false
% 48.04/6.49  --qbf_dom_inst                          none
% 48.04/6.49  --qbf_dom_pre_inst                      false
% 48.04/6.49  --qbf_sk_in                             false
% 48.04/6.49  --qbf_pred_elim                         true
% 48.04/6.49  --qbf_split                             512
% 48.04/6.49  
% 48.04/6.49  ------ BMC1 Options
% 48.04/6.49  
% 48.04/6.49  --bmc1_incremental                      false
% 48.04/6.49  --bmc1_axioms                           reachable_all
% 48.04/6.49  --bmc1_min_bound                        0
% 48.04/6.49  --bmc1_max_bound                        -1
% 48.04/6.49  --bmc1_max_bound_default                -1
% 48.04/6.49  --bmc1_symbol_reachability              true
% 48.04/6.49  --bmc1_property_lemmas                  false
% 48.04/6.49  --bmc1_k_induction                      false
% 48.04/6.49  --bmc1_non_equiv_states                 false
% 48.04/6.49  --bmc1_deadlock                         false
% 48.04/6.49  --bmc1_ucm                              false
% 48.04/6.49  --bmc1_add_unsat_core                   none
% 48.04/6.49  --bmc1_unsat_core_children              false
% 48.04/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 48.04/6.49  --bmc1_out_stat                         full
% 48.04/6.49  --bmc1_ground_init                      false
% 48.04/6.49  --bmc1_pre_inst_next_state              false
% 48.04/6.49  --bmc1_pre_inst_state                   false
% 48.04/6.49  --bmc1_pre_inst_reach_state             false
% 48.04/6.49  --bmc1_out_unsat_core                   false
% 48.04/6.49  --bmc1_aig_witness_out                  false
% 48.04/6.49  --bmc1_verbose                          false
% 48.04/6.49  --bmc1_dump_clauses_tptp                false
% 48.04/6.49  --bmc1_dump_unsat_core_tptp             false
% 48.04/6.49  --bmc1_dump_file                        -
% 48.04/6.49  --bmc1_ucm_expand_uc_limit              128
% 48.04/6.49  --bmc1_ucm_n_expand_iterations          6
% 48.04/6.49  --bmc1_ucm_extend_mode                  1
% 48.04/6.49  --bmc1_ucm_init_mode                    2
% 48.04/6.49  --bmc1_ucm_cone_mode                    none
% 48.04/6.49  --bmc1_ucm_reduced_relation_type        0
% 48.04/6.49  --bmc1_ucm_relax_model                  4
% 48.04/6.49  --bmc1_ucm_full_tr_after_sat            true
% 48.04/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 48.04/6.49  --bmc1_ucm_layered_model                none
% 48.04/6.49  --bmc1_ucm_max_lemma_size               10
% 48.04/6.49  
% 48.04/6.49  ------ AIG Options
% 48.04/6.49  
% 48.04/6.49  --aig_mode                              false
% 48.04/6.49  
% 48.04/6.49  ------ Instantiation Options
% 48.04/6.49  
% 48.04/6.49  --instantiation_flag                    true
% 48.04/6.49  --inst_sos_flag                         false
% 48.04/6.49  --inst_sos_phase                        true
% 48.04/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 48.04/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 48.04/6.49  --inst_lit_sel_side                     none
% 48.04/6.49  --inst_solver_per_active                1400
% 48.04/6.49  --inst_solver_calls_frac                1.
% 48.04/6.49  --inst_passive_queue_type               priority_queues
% 48.04/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 48.04/6.49  --inst_passive_queues_freq              [25;2]
% 48.04/6.49  --inst_dismatching                      true
% 48.04/6.49  --inst_eager_unprocessed_to_passive     true
% 48.04/6.49  --inst_prop_sim_given                   true
% 48.04/6.49  --inst_prop_sim_new                     false
% 48.04/6.49  --inst_subs_new                         false
% 48.04/6.49  --inst_eq_res_simp                      false
% 48.04/6.49  --inst_subs_given                       false
% 48.04/6.49  --inst_orphan_elimination               true
% 48.04/6.49  --inst_learning_loop_flag               true
% 48.04/6.49  --inst_learning_start                   3000
% 48.04/6.49  --inst_learning_factor                  2
% 48.04/6.49  --inst_start_prop_sim_after_learn       3
% 48.04/6.49  --inst_sel_renew                        solver
% 48.04/6.49  --inst_lit_activity_flag                true
% 48.04/6.49  --inst_restr_to_given                   false
% 48.04/6.49  --inst_activity_threshold               500
% 48.04/6.49  --inst_out_proof                        true
% 48.04/6.49  
% 48.04/6.49  ------ Resolution Options
% 48.04/6.49  
% 48.04/6.49  --resolution_flag                       false
% 48.04/6.49  --res_lit_sel                           adaptive
% 48.04/6.49  --res_lit_sel_side                      none
% 48.04/6.49  --res_ordering                          kbo
% 48.04/6.49  --res_to_prop_solver                    active
% 48.04/6.49  --res_prop_simpl_new                    false
% 48.04/6.49  --res_prop_simpl_given                  true
% 48.04/6.49  --res_passive_queue_type                priority_queues
% 48.04/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 48.04/6.49  --res_passive_queues_freq               [15;5]
% 48.04/6.49  --res_forward_subs                      full
% 48.04/6.49  --res_backward_subs                     full
% 48.04/6.49  --res_forward_subs_resolution           true
% 48.04/6.49  --res_backward_subs_resolution          true
% 48.04/6.49  --res_orphan_elimination                true
% 48.04/6.49  --res_time_limit                        2.
% 48.04/6.49  --res_out_proof                         true
% 48.04/6.49  
% 48.04/6.49  ------ Superposition Options
% 48.04/6.49  
% 48.04/6.49  --superposition_flag                    true
% 48.04/6.49  --sup_passive_queue_type                priority_queues
% 48.04/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 48.04/6.49  --sup_passive_queues_freq               [8;1;4]
% 48.04/6.49  --demod_completeness_check              fast
% 48.04/6.49  --demod_use_ground                      true
% 48.04/6.49  --sup_to_prop_solver                    passive
% 48.04/6.49  --sup_prop_simpl_new                    true
% 48.04/6.49  --sup_prop_simpl_given                  true
% 48.04/6.49  --sup_fun_splitting                     false
% 48.04/6.49  --sup_smt_interval                      50000
% 48.04/6.49  
% 48.04/6.49  ------ Superposition Simplification Setup
% 48.04/6.49  
% 48.04/6.49  --sup_indices_passive                   []
% 48.04/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 48.04/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 48.04/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_full_bw                           [BwDemod]
% 48.04/6.49  --sup_immed_triv                        [TrivRules]
% 48.04/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 48.04/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_immed_bw_main                     []
% 48.04/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 48.04/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 48.04/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 48.04/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 48.04/6.49  
% 48.04/6.49  ------ Combination Options
% 48.04/6.49  
% 48.04/6.49  --comb_res_mult                         3
% 48.04/6.49  --comb_sup_mult                         2
% 48.04/6.49  --comb_inst_mult                        10
% 48.04/6.49  
% 48.04/6.49  ------ Debug Options
% 48.04/6.49  
% 48.04/6.49  --dbg_backtrace                         false
% 48.04/6.49  --dbg_dump_prop_clauses                 false
% 48.04/6.49  --dbg_dump_prop_clauses_file            -
% 48.04/6.49  --dbg_out_stat                          false
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  ------ Proving...
% 48.04/6.49  
% 48.04/6.49  
% 48.04/6.49  % SZS status Theorem for theBenchmark.p
% 48.04/6.49  
% 48.04/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 48.04/6.49  
% 48.04/6.49  fof(f12,conjecture,(
% 48.04/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f13,negated_conjecture,(
% 48.04/6.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 48.04/6.49    inference(negated_conjecture,[],[f12])).
% 48.04/6.49  
% 48.04/6.49  fof(f35,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 48.04/6.49    inference(ennf_transformation,[],[f13])).
% 48.04/6.49  
% 48.04/6.49  fof(f36,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f35])).
% 48.04/6.49  
% 48.04/6.49  fof(f48,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 48.04/6.49    inference(nnf_transformation,[],[f36])).
% 48.04/6.49  
% 48.04/6.49  fof(f49,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f48])).
% 48.04/6.49  
% 48.04/6.49  fof(f50,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 48.04/6.49    inference(rectify,[],[f49])).
% 48.04/6.49  
% 48.04/6.49  fof(f54,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f53,plain,(
% 48.04/6.49    ( ! [X0,X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(sK4) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) != k2_struct_0(X0) | ~v3_tops_2(sK4,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(sK4) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X0)) | v3_tops_2(sK4,X0,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f52,plain,(
% 48.04/6.49    ( ! [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : ((? [X3] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,sK3)) & ((! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,sK3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f51,plain,(
% 48.04/6.49    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | v3_tops_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((? [X3] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) != k2_struct_0(sK2) | ~v3_tops_2(X2,sK2,X1)) & ((! [X4] : (k2_pre_topc(X1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(sK2)) | v3_tops_2(X2,sK2,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f55,plain,(
% 48.04/6.49    ((((k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)) & ((! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))) & v2_funct_1(sK4) & k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) & k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)) | v3_tops_2(sK4,sK2,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 48.04/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).
% 48.04/6.49  
% 48.04/6.49  fof(f89,plain,(
% 48.04/6.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f5,axiom,(
% 48.04/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f21,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 48.04/6.49    inference(ennf_transformation,[],[f5])).
% 48.04/6.49  
% 48.04/6.49  fof(f22,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f21])).
% 48.04/6.49  
% 48.04/6.49  fof(f39,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 48.04/6.49    inference(nnf_transformation,[],[f22])).
% 48.04/6.49  
% 48.04/6.49  fof(f40,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 48.04/6.49    inference(rectify,[],[f39])).
% 48.04/6.49  
% 48.04/6.49  fof(f41,plain,(
% 48.04/6.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f42,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 48.04/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 48.04/6.49  
% 48.04/6.49  fof(f68,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f42])).
% 48.04/6.49  
% 48.04/6.49  fof(f84,plain,(
% 48.04/6.49    ~v2_struct_0(sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f85,plain,(
% 48.04/6.49    v2_pre_topc(sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f86,plain,(
% 48.04/6.49    l1_pre_topc(sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f82,plain,(
% 48.04/6.49    v2_pre_topc(sK2)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f83,plain,(
% 48.04/6.49    l1_pre_topc(sK2)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f87,plain,(
% 48.04/6.49    v1_funct_1(sK4)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f88,plain,(
% 48.04/6.49    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f1,axiom,(
% 48.04/6.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f14,plain,(
% 48.04/6.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 48.04/6.49    inference(ennf_transformation,[],[f1])).
% 48.04/6.49  
% 48.04/6.49  fof(f15,plain,(
% 48.04/6.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f14])).
% 48.04/6.49  
% 48.04/6.49  fof(f56,plain,(
% 48.04/6.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f15])).
% 48.04/6.49  
% 48.04/6.49  fof(f3,axiom,(
% 48.04/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f17,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f3])).
% 48.04/6.49  
% 48.04/6.49  fof(f18,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f17])).
% 48.04/6.49  
% 48.04/6.49  fof(f37,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(nnf_transformation,[],[f18])).
% 48.04/6.49  
% 48.04/6.49  fof(f38,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f37])).
% 48.04/6.49  
% 48.04/6.49  fof(f59,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f91,plain,(
% 48.04/6.49    k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | v3_tops_2(sK4,sK2,sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f6,axiom,(
% 48.04/6.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f23,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f6])).
% 48.04/6.49  
% 48.04/6.49  fof(f24,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f23])).
% 48.04/6.49  
% 48.04/6.49  fof(f71,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f24])).
% 48.04/6.49  
% 48.04/6.49  fof(f2,axiom,(
% 48.04/6.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f16,plain,(
% 48.04/6.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f2])).
% 48.04/6.49  
% 48.04/6.49  fof(f57,plain,(
% 48.04/6.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f16])).
% 48.04/6.49  
% 48.04/6.49  fof(f60,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f92,plain,(
% 48.04/6.49    v2_funct_1(sK4) | v3_tops_2(sK4,sK2,sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f9,axiom,(
% 48.04/6.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f29,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f9])).
% 48.04/6.49  
% 48.04/6.49  fof(f30,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f29])).
% 48.04/6.49  
% 48.04/6.49  fof(f74,plain,(
% 48.04/6.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f30])).
% 48.04/6.49  
% 48.04/6.49  fof(f4,axiom,(
% 48.04/6.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f19,plain,(
% 48.04/6.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 48.04/6.49    inference(ennf_transformation,[],[f4])).
% 48.04/6.49  
% 48.04/6.49  fof(f20,plain,(
% 48.04/6.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 48.04/6.49    inference(flattening,[],[f19])).
% 48.04/6.49  
% 48.04/6.49  fof(f64,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f20])).
% 48.04/6.49  
% 48.04/6.49  fof(f65,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f20])).
% 48.04/6.49  
% 48.04/6.49  fof(f66,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f20])).
% 48.04/6.49  
% 48.04/6.49  fof(f7,axiom,(
% 48.04/6.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f25,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f7])).
% 48.04/6.49  
% 48.04/6.49  fof(f26,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f25])).
% 48.04/6.49  
% 48.04/6.49  fof(f72,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f26])).
% 48.04/6.49  
% 48.04/6.49  fof(f69,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK0(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f42])).
% 48.04/6.49  
% 48.04/6.49  fof(f62,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f8,axiom,(
% 48.04/6.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f27,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f8])).
% 48.04/6.49  
% 48.04/6.49  fof(f28,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f27])).
% 48.04/6.49  
% 48.04/6.49  fof(f73,plain,(
% 48.04/6.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f28])).
% 48.04/6.49  
% 48.04/6.49  fof(f67,plain,(
% 48.04/6.49    ( ! [X4,X2,X0,X1] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X4)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f42])).
% 48.04/6.49  
% 48.04/6.49  fof(f63,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v5_pre_topc(X2,X0,X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f10,axiom,(
% 48.04/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f31,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(ennf_transformation,[],[f10])).
% 48.04/6.49  
% 48.04/6.49  fof(f32,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 48.04/6.49    inference(flattening,[],[f31])).
% 48.04/6.49  
% 48.04/6.49  fof(f75,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f32])).
% 48.04/6.49  
% 48.04/6.49  fof(f70,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f24])).
% 48.04/6.49  
% 48.04/6.49  fof(f11,axiom,(
% 48.04/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 48.04/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 48.04/6.49  
% 48.04/6.49  fof(f33,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 48.04/6.49    inference(ennf_transformation,[],[f11])).
% 48.04/6.49  
% 48.04/6.49  fof(f34,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f33])).
% 48.04/6.49  
% 48.04/6.49  fof(f43,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0))) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 48.04/6.49    inference(nnf_transformation,[],[f34])).
% 48.04/6.49  
% 48.04/6.49  fof(f44,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 48.04/6.49    inference(flattening,[],[f43])).
% 48.04/6.49  
% 48.04/6.49  fof(f45,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | ? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 48.04/6.49    inference(rectify,[],[f44])).
% 48.04/6.49  
% 48.04/6.49  fof(f46,plain,(
% 48.04/6.49    ! [X2,X1,X0] : (? [X3] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 48.04/6.49    introduced(choice_axiom,[])).
% 48.04/6.49  
% 48.04/6.49  fof(f47,plain,(
% 48.04/6.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tops_2(X2,X0,X1) | (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)) & ((! [X4] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)) | ~v3_tops_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 48.04/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 48.04/6.49  
% 48.04/6.49  fof(f80,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f47])).
% 48.04/6.49  
% 48.04/6.49  fof(f81,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v3_tops_2(X2,X0,X1) | k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK1(X0,X1,X2))) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK1(X0,X1,X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f47])).
% 48.04/6.49  
% 48.04/6.49  fof(f93,plain,(
% 48.04/6.49    ( ! [X4] : (k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) | v3_tops_2(sK4,sK2,sK3)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f61,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f90,plain,(
% 48.04/6.49    k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) | v3_tops_2(sK4,sK2,sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f58,plain,(
% 48.04/6.49    ( ! [X2,X0,X1] : (k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f38])).
% 48.04/6.49  
% 48.04/6.49  fof(f94,plain,(
% 48.04/6.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  fof(f79,plain,(
% 48.04/6.49    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 48.04/6.49    inference(cnf_transformation,[],[f47])).
% 48.04/6.49  
% 48.04/6.49  fof(f95,plain,(
% 48.04/6.49    k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) | ~v2_funct_1(sK4) | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2) | ~v3_tops_2(sK4,sK2,sK3)),
% 48.04/6.49    inference(cnf_transformation,[],[f55])).
% 48.04/6.49  
% 48.04/6.49  cnf(c_32,negated_conjecture,
% 48.04/6.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 48.04/6.49      inference(cnf_transformation,[],[f89]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1554,negated_conjecture,
% 48.04/6.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_32]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2344,plain,
% 48.04/6.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1554]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_12,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | v5_pre_topc(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | v2_struct_0(X2)
% 48.04/6.49      | ~ v2_pre_topc(X2)
% 48.04/6.49      | ~ v2_pre_topc(X1)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ l1_pre_topc(X2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f68]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37,negated_conjecture,
% 48.04/6.49      ( ~ v2_struct_0(sK3) ),
% 48.04/6.49      inference(cnf_transformation,[],[f84]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_732,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | v5_pre_topc(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ v2_pre_topc(X1)
% 48.04/6.49      | ~ v2_pre_topc(X2)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ l1_pre_topc(X2)
% 48.04/6.49      | sK3 != X2 ),
% 48.04/6.49      inference(resolution_lifted,[status(thm)],[c_12,c_37]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_733,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ v2_pre_topc(X1)
% 48.04/6.49      | ~ v2_pre_topc(sK3)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ l1_pre_topc(sK3) ),
% 48.04/6.49      inference(unflattening,[status(thm)],[c_732]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_36,negated_conjecture,
% 48.04/6.49      ( v2_pre_topc(sK3) ),
% 48.04/6.49      inference(cnf_transformation,[],[f85]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_35,negated_conjecture,
% 48.04/6.49      ( l1_pre_topc(sK3) ),
% 48.04/6.49      inference(cnf_transformation,[],[f86]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_737,plain,
% 48.04/6.49      ( ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ v2_pre_topc(X1) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_733,c_36,c_35]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_738,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ v2_pre_topc(X1)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1) ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_737]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_39,negated_conjecture,
% 48.04/6.49      ( v2_pre_topc(sK2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f82]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1140,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(X1,sK3,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | sK2 != X1 ),
% 48.04/6.49      inference(resolution_lifted,[status(thm)],[c_738,c_39]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1141,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(sK2) ),
% 48.04/6.49      inference(unflattening,[status(thm)],[c_1140]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_38,negated_conjecture,
% 48.04/6.49      ( l1_pre_topc(sK2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f83]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1145,plain,
% 48.04/6.49      ( ~ v1_funct_1(X0)
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.49      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_1141,c_38]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1146,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.49      | ~ v1_funct_1(X0) ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_1145]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1539,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | v5_pre_topc(X0_55,sK2,sK3)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.49      | ~ v1_funct_1(X0_55) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_1146]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2359,plain,
% 48.04/6.49      ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | v5_pre_topc(X0_55,sK2,sK3) = iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1539]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_4102,plain,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2344,c_2359]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_34,negated_conjecture,
% 48.04/6.49      ( v1_funct_1(sK4) ),
% 48.04/6.49      inference(cnf_transformation,[],[f87]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_45,plain,
% 48.04/6.49      ( v1_funct_1(sK4) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_33,negated_conjecture,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 48.04/6.49      inference(cnf_transformation,[],[f88]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_46,plain,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_4131,plain,
% 48.04/6.49      ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.49      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_4102,c_45,c_46]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_4132,plain,
% 48.04/6.49      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 48.04/6.49      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_4131]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_0,plain,
% 48.04/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.49      | ~ l1_pre_topc(X1) ),
% 48.04/6.49      inference(cnf_transformation,[],[f56]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1574,plain,
% 48.04/6.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_57)))
% 48.04/6.49      | m1_subset_1(k2_pre_topc(X0_57,X0_55),k1_zfmisc_1(u1_struct_0(X0_57)))
% 48.04/6.49      | ~ l1_pre_topc(X0_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_0]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2324,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 48.04/6.49      | m1_subset_1(k2_pre_topc(X0_57,X0_55),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 48.04/6.49      | l1_pre_topc(X0_57) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_6,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ l1_pre_topc(X2)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f59]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1568,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.49      | ~ v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | ~ l1_pre_topc(X1_57)
% 48.04/6.49      | ~ l1_pre_topc(X0_57)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X1_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_6]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2330,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X1_57)
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 48.04/6.49      | v3_tops_2(X0_55,X0_57,X1_57) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | l1_pre_topc(X0_57) != iProver_top
% 48.04/6.49      | l1_pre_topc(X1_57) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3722,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 48.04/6.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2344,c_2330]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_30,negated_conjecture,
% 48.04/6.49      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.49      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.49      inference(cnf_transformation,[],[f91]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1556,negated_conjecture,
% 48.04/6.49      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.49      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_30]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1579,plain,
% 48.04/6.49      ( X0_59 != X1_59 | X2_59 != X1_59 | X2_59 = X0_59 ),
% 48.04/6.49      theory(equality) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3085,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != X0_59
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) = k2_struct_0(sK3)
% 48.04/6.49      | k2_struct_0(sK3) != X0_59 ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1579]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3231,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) = k2_struct_0(sK3)
% 48.04/6.49      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_3085]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3232,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
% 48.04/6.49      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_3231]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1577,plain,( X0_59 = X0_59 ),theory(equality) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3252,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1577]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3754,plain,
% 48.04/6.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.49      | ~ v1_funct_1(sK4)
% 48.04/6.49      | ~ l1_pre_topc(sK2)
% 48.04/6.49      | ~ l1_pre_topc(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 48.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3722]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3921,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_3722,c_38,c_35,c_34,c_33,c_1556,c_3232,c_3252,c_3754]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_14,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | v2_struct_0(X2)
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v2_funct_1(X0)
% 48.04/6.49      | ~ l1_struct_0(X2)
% 48.04/6.49      | ~ l1_struct_0(X1)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 48.04/6.49      inference(cnf_transformation,[],[f71]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_666,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v2_funct_1(X0)
% 48.04/6.49      | ~ l1_struct_0(X1)
% 48.04/6.49      | ~ l1_struct_0(X2)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 48.04/6.49      | sK3 != X2 ),
% 48.04/6.49      inference(resolution_lifted,[status(thm)],[c_14,c_37]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_667,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v2_funct_1(X0)
% 48.04/6.49      | ~ l1_struct_0(X1)
% 48.04/6.49      | ~ l1_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0)) = k2_struct_0(X1) ),
% 48.04/6.49      inference(unflattening,[status(thm)],[c_666]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1547,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | ~ v2_funct_1(X0_55)
% 48.04/6.49      | ~ l1_struct_0(X0_57)
% 48.04/6.49      | ~ l1_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_667]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2351,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.49      | l1_struct_0(X0_57) != iProver_top
% 48.04/6.49      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_44,plain,
% 48.04/6.49      ( l1_pre_topc(sK3) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1666,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.49      | l1_struct_0(X0_57) != iProver_top
% 48.04/6.49      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1,plain,
% 48.04/6.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 48.04/6.49      inference(cnf_transformation,[],[f57]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1573,plain,
% 48.04/6.49      ( l1_struct_0(X0_57) | ~ l1_pre_topc(X0_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_1]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2899,plain,
% 48.04/6.49      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1573]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2900,plain,
% 48.04/6.49      ( l1_struct_0(sK3) = iProver_top
% 48.04/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2899]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3624,plain,
% 48.04/6.49      ( l1_struct_0(X0_57) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_2351,c_44,c_1666,c_2900]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3625,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57)
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.49      | l1_struct_0(X0_57) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_3624]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3926,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2)
% 48.04/6.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top
% 48.04/6.49      | v2_funct_1(sK4) != iProver_top
% 48.04/6.49      | l1_struct_0(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_3921,c_3625]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_129,plain,
% 48.04/6.49      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_5,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | v2_funct_1(X0)
% 48.04/6.49      | ~ l1_pre_topc(X1)
% 48.04/6.49      | ~ l1_pre_topc(X2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f60]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1569,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.49      | ~ v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | v2_funct_1(X0_55)
% 48.04/6.49      | ~ l1_pre_topc(X1_57)
% 48.04/6.49      | ~ l1_pre_topc(X0_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_5]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2329,plain,
% 48.04/6.49      ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 48.04/6.49      | v3_tops_2(X0_55,X0_57,X1_57) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) = iProver_top
% 48.04/6.49      | l1_pre_topc(X0_57) != iProver_top
% 48.04/6.49      | l1_pre_topc(X1_57) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3328,plain,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top
% 48.04/6.49      | v2_funct_1(sK4) = iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2344,c_2329]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_41,plain,
% 48.04/6.49      ( l1_pre_topc(sK2) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_29,negated_conjecture,
% 48.04/6.49      ( v3_tops_2(sK4,sK2,sK3) | v2_funct_1(sK4) ),
% 48.04/6.49      inference(cnf_transformation,[],[f92]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_50,plain,
% 48.04/6.49      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.49      | v2_funct_1(sK4) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3426,plain,
% 48.04/6.49      ( v2_funct_1(sK4) = iProver_top ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_3328,c_41,c_44,c_45,c_46,c_50]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3428,plain,
% 48.04/6.49      ( v2_funct_1(sK4) ),
% 48.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3426]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3626,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | ~ v2_funct_1(X0_55)
% 48.04/6.49      | ~ l1_struct_0(X0_57)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(X0_57) ),
% 48.04/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3625]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3628,plain,
% 48.04/6.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(sK4)
% 48.04/6.49      | ~ v2_funct_1(sK4)
% 48.04/6.49      | ~ l1_struct_0(sK2)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_3626]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_4600,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK2) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_3926,c_38,c_35,c_34,c_33,c_32,c_129,c_1556,c_3232,
% 48.04/6.49                 c_3252,c_3428,c_3628,c_3754]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_18,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v2_funct_1(X0)
% 48.04/6.49      | ~ l1_struct_0(X2)
% 48.04/6.49      | ~ l1_struct_0(X1)
% 48.04/6.49      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f74]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1561,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_57)))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | ~ v2_funct_1(X0_55)
% 48.04/6.49      | ~ l1_struct_0(X1_57)
% 48.04/6.49      | ~ l1_struct_0(X0_57)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
% 48.04/6.49      | k7_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_18]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2337,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
% 48.04/6.49      | k7_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k8_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55)
% 48.04/6.49      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 48.04/6.49      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X1_57))) != iProver_top
% 48.04/6.49      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.49      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.49      | l1_struct_0(X0_57) != iProver_top
% 48.04/6.49      | l1_struct_0(X1_57) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_4603,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)
% 48.04/6.49      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.49      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.49      | l1_struct_0(sK2) != iProver_top
% 48.04/6.49      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_4600,c_2337]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_47,plain,
% 48.04/6.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_128,plain,
% 48.04/6.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_130,plain,
% 48.04/6.49      ( l1_struct_0(sK2) = iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_128]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_10,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 48.04/6.49      inference(cnf_transformation,[],[f64]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1564,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,X0_56,X1_56)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | v1_funct_1(k2_tops_2(X0_56,X1_56,X0_55)) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_10]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2936,plain,
% 48.04/6.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.49      | ~ v1_funct_1(sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1564]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2937,plain,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2936]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_9,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,X1,X2)
% 48.04/6.49      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 48.04/6.49      | ~ v1_funct_1(X0) ),
% 48.04/6.49      inference(cnf_transformation,[],[f65]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1565,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,X0_56,X1_56)
% 48.04/6.49      | v1_funct_2(k2_tops_2(X0_56,X1_56,X0_55),X1_56,X0_56)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 48.04/6.49      | ~ v1_funct_1(X0_55) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_9]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2939,plain,
% 48.04/6.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.49      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1565]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2940,plain,
% 48.04/6.49      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 48.04/6.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2939]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,X1,X2)
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 48.04/6.49      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 48.04/6.49      | ~ v1_funct_1(X0) ),
% 48.04/6.49      inference(cnf_transformation,[],[f66]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1566,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,X0_56,X1_56)
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 48.04/6.49      | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56)))
% 48.04/6.49      | ~ v1_funct_1(X0_55) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_8]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2942,plain,
% 48.04/6.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(sK4) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1566]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_2943,plain,
% 48.04/6.49      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top
% 48.04/6.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_2942]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_16,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.49      | ~ v1_funct_1(X0)
% 48.04/6.49      | ~ v2_funct_1(X0)
% 48.04/6.49      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 48.04/6.49      | ~ l1_struct_0(X2)
% 48.04/6.49      | ~ l1_struct_0(X1)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.49      inference(cnf_transformation,[],[f72]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_1563,plain,
% 48.04/6.49      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.49      | ~ v1_funct_1(X0_55)
% 48.04/6.49      | ~ v2_funct_1(X0_55)
% 48.04/6.49      | v2_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55))
% 48.04/6.49      | ~ l1_struct_0(X1_57)
% 48.04/6.49      | ~ l1_struct_0(X0_57)
% 48.04/6.49      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57) ),
% 48.04/6.49      inference(subtyping,[status(esa)],[c_16]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3091,plain,
% 48.04/6.49      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.49      | ~ v1_funct_1(sK4)
% 48.04/6.49      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.49      | ~ v2_funct_1(sK4)
% 48.04/6.49      | ~ l1_struct_0(sK2)
% 48.04/6.49      | ~ l1_struct_0(sK3)
% 48.04/6.49      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3) ),
% 48.04/6.49      inference(instantiation,[status(thm)],[c_1563]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_3092,plain,
% 48.04/6.49      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.49      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.49      | v1_funct_1(sK4) != iProver_top
% 48.04/6.49      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = iProver_top
% 48.04/6.49      | v2_funct_1(sK4) != iProver_top
% 48.04/6.49      | l1_struct_0(sK2) != iProver_top
% 48.04/6.49      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.49      inference(predicate_to_equality,[status(thm)],[c_3091]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8409,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_4603,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_47,
% 48.04/6.49                 c_50,c_130,c_1556,c_2900,c_2937,c_2940,c_2943,c_3092,
% 48.04/6.49                 c_3232,c_3252,c_3328,c_3754]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8410,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),X0_55) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_8409]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8418,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_8410]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8454,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_8418,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8455,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_8454]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8463,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_8455]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8621,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_8463,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8622,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_8621]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8630,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_8622]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8666,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_8630,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8667,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_8666]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8675,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_8667]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8728,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_8675,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8729,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_8728]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_8737,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_8729]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_10115,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_8737,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_10116,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_10115]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_10124,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_10116]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_12834,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_10124,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_12835,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_12834]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_12843,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_12835]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_14215,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_12843,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_14216,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_14215]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_14224,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_14216]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_16243,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_14224,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_16244,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_16243]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_16252,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_16244]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_17019,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_16252,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_17020,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_17019]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_17028,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_17020]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_19199,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_17028,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_19200,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_19199]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_19208,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_19200]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_20550,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_19208,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_20551,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_20550]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_20559,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_20551]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_23136,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_20559,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_23137,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_23136]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_23145,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_23137]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_24446,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_23145,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_24447,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_24446]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_24455,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_24447]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_27016,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_24455,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_27017,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_27016]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_27025,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_27017]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_28299,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_27025,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_28300,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_28299]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_28308,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_28300]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_31978,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_28308,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_31979,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_31978]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_31987,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_31979]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_33457,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_31987,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_33458,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_33457]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_33466,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_33458]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37051,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_33466,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37052,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_37051]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37060,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_37052]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37902,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_37060,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37903,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_37902]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_37911,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_37903]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_40297,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_37911,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_40298,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_40297]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_40306,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_40298]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_41141,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_40306,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_41142,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_41141]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_41150,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_41142]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_43809,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_41150,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_43810,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_43809]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_43818,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_43810]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_44954,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_43818,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_44955,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_44954]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_44963,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_44955]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_47909,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_44963,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_47910,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_47909]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_47918,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_47910]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_49784,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_47918,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_49785,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_49784]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_49793,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_49785]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_54555,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_49793,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_54556,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_54555]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_54564,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_54556]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_56397,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_54564,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_56398,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_56397]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_56406,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_56398]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_60109,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_56406,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_60110,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_60109]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_60118,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_60110]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_61038,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_60118,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_61039,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_61038]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_61047,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.49      inference(superposition,[status(thm)],[c_2324,c_61039]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_64084,plain,
% 48.04/6.49      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.49      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) ),
% 48.04/6.49      inference(global_propositional_subsumption,
% 48.04/6.49                [status(thm)],
% 48.04/6.49                [c_61047,c_41]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_64085,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))
% 48.04/6.49      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.49      inference(renaming,[status(thm)],[c_64084]) ).
% 48.04/6.49  
% 48.04/6.49  cnf(c_64093,plain,
% 48.04/6.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_64085]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_65147,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_64093,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_65148,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_65147]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_65156,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_65148]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_68608,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_65156,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_68609,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_68608]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_68617,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_68609]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69904,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_68617,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69905,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_69904]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69913,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_69905]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_73883,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_69913,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_73884,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_73883]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_73892,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_73884]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75440,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_73892,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75441,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_75440]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75449,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_75441]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_79397,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_75449,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_79398,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_79397]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_79406,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_79398]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_80720,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_79406,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_80721,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_80720]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_80729,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_80721]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_84299,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_80729,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_84300,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_84299]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_84308,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_84300]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_85847,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_84308,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_85848,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_85847]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_85856,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_85848]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_90018,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_85856,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_90019,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_90018]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_90027,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_90019]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_92151,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_90027,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_92152,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_92151]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_92160,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_92152]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96029,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_92160,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96030,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_96029]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96039,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))))))))))))))))))))))))))))))))))))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))))))))))))))))))))))))))))))))))))))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_96030]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1576,plain,( X0_55 = X0_55 ),theory(equality) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1605,plain,
% 48.04/6.50      ( sK4 = sK4 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_11,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | v2_struct_0(X2)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f69]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_765,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,sK0(X1,X2,X0))),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | sK3 != X2 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_11,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_766,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(sK3)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_765]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_770,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v2_pre_topc(X1) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_766,c_36,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_771,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_770]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1113,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,sK0(X1,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,sK0(X1,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | sK2 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_771,c_39]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1114,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(sK2) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_1113]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1118,plain,
% 48.04/6.50      ( ~ v1_funct_1(X0)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
% 48.04/6.50      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_1114,c_38]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1119,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,sK0(sK2,sK3,X0))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,sK0(sK2,sK3,X0))))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_1118]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1540,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | v5_pre_topc(X0_55,sK2,sK3)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X0_55))))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0_55) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_1119]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1687,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(X0_55,sK2,sK3) = iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X0_55)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1540]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1689,plain,
% 48.04/6.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1687]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f62]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1571,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57)
% 48.04/6.50      | ~ v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ l1_pre_topc(X1_57)
% 48.04/6.50      | ~ l1_pre_topc(X0_57) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_3]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2995,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57))
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)),X0_57,sK3)
% 48.04/6.50      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55))
% 48.04/6.50      | ~ l1_pre_topc(X0_57)
% 48.04/6.50      | ~ l1_pre_topc(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1571]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2996,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)),X0_57,sK3) = iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) != iProver_top
% 48.04/6.50      | l1_pre_topc(X0_57) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_2995]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2998,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) = iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_2996]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3002,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1564]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3008,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3002]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3001,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1565]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3010,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3001]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3000,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1566]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3012,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3000]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4562,plain,
% 48.04/6.50      ( sK0(sK2,sK3,X0_55) = sK0(sK2,sK3,X0_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4564,plain,
% 48.04/6.50      ( sK0(sK2,sK3,sK4) = sK0(sK2,sK3,sK4) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_4562]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_17,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_struct_0(X2)
% 48.04/6.50      | ~ l1_struct_0(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f73]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1562,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_57)))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | ~ l1_struct_0(X1_57)
% 48.04/6.50      | ~ l1_struct_0(X0_57)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k7_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_17]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2336,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1_57),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_55) = k7_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55,X1_55)
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(X0_57))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_struct_0(X0_57) != iProver_top
% 48.04/6.50      | l1_struct_0(X1_57) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3928,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_struct_0(sK2) != iProver_top
% 48.04/6.50      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_3921,c_2336]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5063,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_3928,c_41,c_44,c_45,c_46,c_47,c_50,c_130,c_2900,
% 48.04/6.50                 c_3328]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5064,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_5063]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5073,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_5064]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5072,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_5064]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5603,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_5072,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5604,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_5603]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5613,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_5604]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8419,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_8410]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8464,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_8455]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_13,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | v2_struct_0(X2)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f67]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_696,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X1,X3)),k2_pre_topc(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | sK3 != X2 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_13,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_697,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(sK3)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_696]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_701,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_697,c_36,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_702,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_701]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1167,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,k2_pre_topc(X1,X2)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0,X2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | sK2 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_702,c_39]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1168,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(sK2) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_1167]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1172,plain,
% 48.04/6.50      ( ~ v1_funct_1(X0)
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
% 48.04/6.50      | ~ v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_1168,c_38]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1173,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0,sK2,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,k2_pre_topc(sK2,X1)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0,X1)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_1172]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1538,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0_55,sK2,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,X1_55)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55)))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_1173]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3477,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(X0_55,sK2,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X1_55))))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1538]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8560,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK2,sK3)
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))))
% 48.04/6.50      | ~ m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3477]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8573,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)))) = iProver_top
% 48.04/6.50      | m1_subset_1(sK0(sK2,sK3,X1_55),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55))) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_8560]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8575,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))) = iProver_top
% 48.04/6.50      | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_8573]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 48.04/6.50      | v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f63]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1572,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.50      | ~ v5_pre_topc(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57)
% 48.04/6.50      | v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | ~ l1_pre_topc(X1_57)
% 48.04/6.50      | ~ l1_pre_topc(X0_57)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X0_57)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_2]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2326,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X0_57)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) != k2_struct_0(X1_57)
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 48.04/6.50      | v5_pre_topc(X0_55,X0_57,X1_57) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55),X1_57,X0_57) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,X0_57,X1_57) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_pre_topc(X0_57) != iProver_top
% 48.04/6.50      | l1_pre_topc(X1_57) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4606,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK2,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4600,c_2326]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_19,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | v2_struct_0(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f75]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_606,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | sK3 != X2 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_19,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_607,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,sK3)
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_606]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_611,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
% 48.04/6.50      | ~ v3_tops_2(X0,X1,sK3)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_607,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_612,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,sK3)
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0),sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_611]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1549,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
% 48.04/6.50      | ~ v3_tops_2(X0_55,X0_57,sK3)
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ l1_pre_topc(X0_57) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_612]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1660,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,X0_57,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_pre_topc(X0_57) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1662,plain,
% 48.04/6.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1660]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_15,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | v2_struct_0(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_struct_0(X2)
% 48.04/6.50      | ~ l1_struct_0(X1)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f70]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_636,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_struct_0(X1)
% 48.04/6.50      | ~ l1_struct_0(X2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X2)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 48.04/6.50      | sK3 != X2 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_15,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_637,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_struct_0(X1)
% 48.04/6.50      | ~ l1_struct_0(sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK3),X0)) = k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK3),X0) != k2_struct_0(sK3) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_636]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1548,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | ~ l1_struct_0(X0_57)
% 48.04/6.50      | ~ l1_struct_0(sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_637]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1663,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0_57),k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) = k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | v2_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_struct_0(X0_57) != iProver_top
% 48.04/6.50      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1665,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) = k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_struct_0(sK2) != iProver_top
% 48.04/6.50      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1663]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_21,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 48.04/6.50      | v2_struct_0(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f80]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_522,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 48.04/6.50      | sK3 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_21,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_523,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(sK3)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_522]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_527,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_523,c_36,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_528,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_527]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1233,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1)
% 48.04/6.50      | sK2 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_528,c_39]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1234,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(sK2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_1233]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1238,plain,
% 48.04/6.50      ( ~ v2_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_1234,c_38]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1239,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_1238]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1536,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0_55,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_1239]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3079,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.50      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1536]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3080,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3079]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_20,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | v2_struct_0(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f81]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_564,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,sK1(X1,X2,X0))) != k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK1(X1,X2,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
% 48.04/6.50      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 48.04/6.50      | sK3 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_20,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_565,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(sK3)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_564]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_569,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_565,c_36,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_570,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_569]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1197,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,sK1(sK3,X1,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,sK1(sK3,X1,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0) != k2_struct_0(X1)
% 48.04/6.50      | sK2 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_570,c_39]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1198,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(sK2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_1197]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1202,plain,
% 48.04/6.50      ( ~ v2_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_1198,c_38]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1203,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v2_funct_1(X0)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK1(sK3,sK2,X0))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,sK1(sK3,sK2,X0)))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0) != k2_struct_0(sK2) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_1202]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1537,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(X0_55,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55) != k2_struct_0(sK2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,sK1(sK3,sK2,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,sK1(sK3,sK2,X0_55))) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_1203]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3082,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.50      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1537]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3083,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | v2_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3082]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_28,negated_conjecture,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0)) ),
% 48.04/6.50      inference(cnf_transformation,[],[f93]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1558,negated_conjecture,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_28]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3151,plain,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1558]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3152,plain,
% 48.04/6.50      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3151]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3164,plain,
% 48.04/6.50      ( ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ l1_pre_topc(sK2) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1574]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3165,plain,
% 48.04/6.50      ( m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3164]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3159,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_57))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57))))
% 48.04/6.50      | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | ~ l1_struct_0(X0_57)
% 48.04/6.50      | ~ l1_struct_0(sK2)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55) != k2_struct_0(X0_57)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1562]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3599,plain,
% 48.04/6.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(sK4)
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | ~ l1_struct_0(sK2)
% 48.04/6.50      | ~ l1_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3159]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3600,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_struct_0(sK2) != iProver_top
% 48.04/6.50      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3599]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1578,plain,
% 48.04/6.50      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 48.04/6.50      theory(equality) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3452,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3779,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3452]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3780,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3552,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(X0_57))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_57))))
% 48.04/6.50      | ~ m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ v2_funct_1(X0_55)
% 48.04/6.50      | ~ l1_struct_0(X0_57)
% 48.04/6.50      | ~ l1_struct_0(sK2)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55) != k2_struct_0(X0_57)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X0_57),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_57),X0_55,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1562]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4031,plain,
% 48.04/6.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(sK4)
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | ~ l1_struct_0(sK2)
% 48.04/6.50      | ~ l1_struct_0(sK3)
% 48.04/6.50      | k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3552]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4032,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_struct_0(sK2) != iProver_top
% 48.04/6.50      | l1_struct_0(sK3) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_4031]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3781,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X1_55
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = X0_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4518,plain,
% 48.04/6.50      ( X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = X0_55
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3781]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4800,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_4518]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4486,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != X0_55
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5918,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))))
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_4486]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1580,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | k2_pre_topc(X0_57,X0_55) = k2_pre_topc(X0_57,X1_55) ),
% 48.04/6.50      theory(equality) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5939,plain,
% 48.04/6.50      ( X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 48.04/6.50      | k2_pre_topc(sK3,X0_55) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1580]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_6180,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))
% 48.04/6.50      | k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK1(sK3,sK2,k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_5939]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_9944,plain,
% 48.04/6.50      ( v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4606,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_3080,c_3083,c_3092,c_3152,c_3165,
% 48.04/6.50                 c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,
% 48.04/6.50                 c_3780,c_4032,c_4800,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_7049,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_36987,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_7049]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_36989,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_36987]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1589,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X2_55 != X3_55
% 48.04/6.50      | k7_relset_1(X0_56,X1_56,X0_55,X2_55) = k7_relset_1(X0_56,X1_56,X1_55,X3_55) ),
% 48.04/6.50      theory(equality) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_7055,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X2_55 != X3_55
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X2_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X1_55,X3_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1589]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_37643,plain,
% 48.04/6.50      ( X0_55 != sK0(sK2,sK3,X1_55)
% 48.04/6.50      | X2_55 != sK4
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2_55,X0_55) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_7055]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_44951,plain,
% 48.04/6.50      ( X0_55 != sK4
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,sK0(sK2,sK3,X1_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55))
% 48.04/6.50      | sK0(sK2,sK3,X1_55) != sK0(sK2,sK3,X1_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_37643]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_44952,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
% 48.04/6.50      | sK0(sK2,sK3,sK4) != sK0(sK2,sK3,sK4)
% 48.04/6.50      | sK4 != sK4 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_44951]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_63383,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)) != X2_55
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))) = k2_pre_topc(sK3,X2_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1580]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_64850,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK0(sK2,sK3,X1_55))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)),sK0(sK2,sK3,X1_55))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK0(sK2,sK3,X1_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_63383]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_64851,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_64850]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_64646,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))) != X1_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_67930,plain,
% 48.04/6.50      ( X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55)))
% 48.04/6.50      | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55)))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X1_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_64646]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69832,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_67930]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69834,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_69832]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_66745,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),sK0(sK2,sK3,X3_55))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55),sK0(sK2,sK3,X3_55)) != X1_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_68340,plain,
% 48.04/6.50      ( X0_55 = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X1_55))
% 48.04/6.50      | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X1_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X1_55)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_66745]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69960,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_68340]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_69962,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_69960]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_62242,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X0_55 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))) != X1_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_63371,plain,
% 48.04/6.50      ( X0_55 != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
% 48.04/6.50      | X0_55 = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_62242]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75126,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_63371]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75127,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_75126]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_68567,plain,
% 48.04/6.50      ( X0_55 != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))
% 48.04/6.50      | k2_pre_topc(sK3,X0_55) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1580]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75360,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_68567]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_75365,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_75360]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_62785,plain,
% 48.04/6.50      ( X0_55 != X1_55
% 48.04/6.50      | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) != X1_55 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_63382,plain,
% 48.04/6.50      ( X0_55 != k2_pre_topc(sK3,X1_55)
% 48.04/6.50      | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) != k2_pre_topc(sK3,X1_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_62785]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_66741,plain,
% 48.04/6.50      ( X0_55 != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55)))
% 48.04/6.50      | X0_55 = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),sK0(sK2,sK3,X2_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55)),sK0(sK2,sK3,X2_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X1_55),sK0(sK2,sK3,X2_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_63382]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_85839,plain,
% 48.04/6.50      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_66741]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_85841,plain,
% 48.04/6.50      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_85839]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1590,plain,
% 48.04/6.50      ( ~ r1_tarski(X0_55,X1_55)
% 48.04/6.50      | r1_tarski(X2_55,X3_55)
% 48.04/6.50      | X2_55 != X0_55
% 48.04/6.50      | X3_55 != X1_55 ),
% 48.04/6.50      theory(equality) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_61114,plain,
% 48.04/6.50      ( r1_tarski(X0_55,X1_55)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))))
% 48.04/6.50      | X0_55 != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X3_55)))
% 48.04/6.50      | X1_55 != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X2_55)),sK0(sK2,sK3,X3_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1590]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_62244,plain,
% 48.04/6.50      ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55),X2_55)
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X4_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),sK0(sK2,sK3,X4_55))))
% 48.04/6.50      | X2_55 != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),sK0(sK2,sK3,X4_55)))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X3_55)),k2_pre_topc(sK2,sK0(sK2,sK3,X4_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_61114]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_84611,plain,
% 48.04/6.50      ( r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X2_55))))
% 48.04/6.50      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X2_55))))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X2_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X2_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X2_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_62244]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_95822,plain,
% 48.04/6.50      ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))))
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55))) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_84611]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_95823,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55)))
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,X0_55)))) != iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,X0_55))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,X0_55)))) = iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_95822]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_95825,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4))) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),k2_tops_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)),sK0(sK2,sK3,sK4)))) != iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)))) = iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_95823]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96447,plain,
% 48.04/6.50      ( v5_pre_topc(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_96039,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1605,c_1556,c_1662,c_1665,
% 48.04/6.50                 c_1689,c_2900,c_2937,c_2940,c_2943,c_2998,c_3008,c_3010,
% 48.04/6.50                 c_3012,c_3080,c_3083,c_3092,c_3152,c_3165,c_3232,c_3252,
% 48.04/6.50                 c_3328,c_3428,c_3600,c_3628,c_3754,c_3779,c_3780,c_4032,
% 48.04/6.50                 c_4132,c_4564,c_4800,c_5073,c_5613,c_5918,c_6180,c_8419,
% 48.04/6.50                 c_8464,c_8575,c_36989,c_44952,c_64851,c_69834,c_69962,
% 48.04/6.50                 c_75127,c_75365,c_85841,c_95825]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2340,plain,
% 48.04/6.50      ( k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3060,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_2340]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4251,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_3060,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4252,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,X0_55)))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4251]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4260,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_4252]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4281,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4260,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4282,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4281]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4290,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_4282]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4381,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4290,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4382,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4381]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4390,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_4382]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4829,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4390,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4830,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4829]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4839,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_4830]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4860,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4839,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4861,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4860]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4870,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2324,c_4861]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4919,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4870,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4920,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55)))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,X0_55))))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4919]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4930,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_4920]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | v5_pre_topc(X0,X1,X2)
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f61]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1570,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.50      | v5_pre_topc(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ l1_pre_topc(X1_57)
% 48.04/6.50      | ~ l1_pre_topc(X0_57) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_4]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2956,plain,
% 48.04/6.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57))
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
% 48.04/6.50      | ~ v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57)
% 48.04/6.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57))))
% 48.04/6.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55))
% 48.04/6.50      | ~ l1_pre_topc(X0_57)
% 48.04/6.50      | ~ l1_pre_topc(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1570]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2957,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(X0_57)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_57)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)) != iProver_top
% 48.04/6.50      | l1_pre_topc(X0_57) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_2956]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2959,plain,
% 48.04/6.50      ( v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) = iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_2957]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3930,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_3921,c_2326]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_31,negated_conjecture,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 48.04/6.50      inference(cnf_transformation,[],[f90]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1555,negated_conjecture,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_31]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2343,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1555]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_7,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
% 48.04/6.50      inference(cnf_transformation,[],[f58]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1567,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 48.04/6.50      | ~ v3_tops_2(X0_55,X0_57,X1_57)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | ~ l1_pre_topc(X1_57)
% 48.04/6.50      | ~ l1_pre_topc(X0_57)
% 48.04/6.50      | k1_relset_1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_55) = k2_struct_0(X0_57) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_7]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2961,plain,
% 48.04/6.50      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(sK4)
% 48.04/6.50      | ~ l1_pre_topc(sK2)
% 48.04/6.50      | ~ l1_pre_topc(sK3)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1567]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3023,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK2) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_2343,c_38,c_35,c_34,c_33,c_32,c_1555,c_2961]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3941,plain,
% 48.04/6.50      ( k2_struct_0(sK2) != k2_struct_0(sK2)
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(light_normalisation,[status(thm)],[c_3930,c_3023]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3942,plain,
% 48.04/6.50      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK3) != iProver_top ),
% 48.04/6.50      inference(equality_resolution_simp,[status(thm)],[c_3941]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4950,plain,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_3942,c_41,c_44,c_45,c_46,c_47,c_50,c_3328]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4951,plain,
% 48.04/6.50      ( v5_pre_topc(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK3,sK2) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4950]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_6599,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4930,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,
% 48.04/6.50                 c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,
% 48.04/6.50                 c_3779,c_3780,c_4032,c_4800,c_4951,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_27,negated_conjecture,
% 48.04/6.50      ( ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.50      inference(cnf_transformation,[],[f94]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1559,negated_conjecture,
% 48.04/6.50      ( ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_27]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2339,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3027,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k2_struct_0(sK2) != k2_struct_0(sK2)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(demodulation,[status(thm)],[c_3023,c_2339]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3028,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(equality_resolution_simp,[status(thm)],[c_3027]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1648,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3413,plain,
% 48.04/6.50      ( k2_struct_0(sK3) = k2_struct_0(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1577]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3234,plain,
% 48.04/6.50      ( X0_59 != X1_59
% 48.04/6.50      | k2_struct_0(sK3) != X1_59
% 48.04/6.50      | k2_struct_0(sK3) = X0_59 ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1579]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3412,plain,
% 48.04/6.50      ( X0_59 != k2_struct_0(sK3)
% 48.04/6.50      | k2_struct_0(sK3) = X0_59
% 48.04/6.50      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3234]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3608,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55) != k2_struct_0(sK3)
% 48.04/6.50      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55)
% 48.04/6.50      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3412]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3609,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k2_struct_0(sK3) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.50      | k2_struct_0(sK3) != k2_struct_0(sK3) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_3608]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4542,plain,
% 48.04/6.50      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_3028,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_50,c_1648,c_1556,c_1555,c_2961,c_3232,c_3252,c_3328,
% 48.04/6.50                 c_3413,c_3609,c_3754]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4543,plain,
% 48.04/6.50      ( v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_4542]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5611,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4543,c_5604]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8202,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_6599,c_5611]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2360,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(X0_55,sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,k2_pre_topc(sK2,X1_55)),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X0_55,X1_55))) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_56160,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_8202,c_2360]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_56870,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_56160,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,
% 48.04/6.50                 c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,
% 48.04/6.50                 c_3779,c_3780,c_4032,c_4800,c_4951,c_5611,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96457,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_96447,c_56870]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5071,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4543,c_5064]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_8183,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_6599,c_5071]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_49465,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))))) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_8183,c_2360]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_50081,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_49465,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,
% 48.04/6.50                 c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,
% 48.04/6.50                 c_3779,c_3780,c_4032,c_4800,c_4951,c_5071,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96458,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_96447,c_50081]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_4840,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) = iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4132,c_4830]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_6416,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) = iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_4840,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,
% 48.04/6.50                 c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,
% 48.04/6.50                 c_3779,c_3780,c_4032,c_4800,c_4951,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2349,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(X0_57),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,X0_57,sK3) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(X0_57),u1_struct_0(sK3),X0_55),sK3,X0_57) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_pre_topc(X0_57) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2332,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,X0_56,X1_56) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 48.04/6.50      | m1_subset_1(k2_tops_2(X0_56,X1_56,X0_55),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) = iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_22,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 48.04/6.50      | v2_struct_0(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) ),
% 48.04/6.50      inference(cnf_transformation,[],[f79]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_486,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 48.04/6.50      | ~ v3_tops_2(X0,X1,X2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 48.04/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(X2)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(X2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_pre_topc(X2,X3)) = k2_pre_topc(X1,k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
% 48.04/6.50      | sK3 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_22,c_37]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_487,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v2_pre_topc(sK3)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ l1_pre_topc(sK3)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_486]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_491,plain,
% 48.04/6.50      ( ~ l1_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_487,c_36,c_35]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_492,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v2_pre_topc(X1)
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2)) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_491]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1269,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,X1)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 48.04/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(X1)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X0,X2))
% 48.04/6.50      | sK2 != X1 ),
% 48.04/6.50      inference(resolution_lifted,[status(thm)],[c_492,c_39]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1270,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | ~ l1_pre_topc(sK2)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
% 48.04/6.50      inference(unflattening,[status(thm)],[c_1269]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1274,plain,
% 48.04/6.50      ( ~ v1_funct_1(X0)
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_1270,c_38]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1275,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ v3_tops_2(X0,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0,X1)) ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_1274]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1535,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ v3_tops_2(X0_55,sK3,sK2)
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 48.04/6.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,X1_55)) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_1275]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2363,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),X0_55,X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,sK3,sK2) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1535]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3463,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2332,c_2363]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3069,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0_55)
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1564]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3073,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55)) = iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3069]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3068,plain,
% 48.04/6.50      ( ~ v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3))
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2))
% 48.04/6.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 48.04/6.50      | ~ v1_funct_1(X0_55) ),
% 48.04/6.50      inference(instantiation,[status(thm)],[c_1565]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3075,plain,
% 48.04/6.50      ( v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_3068]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5251,plain,
% 48.04/6.50      ( v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_3463,c_3073,c_3075]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5252,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),sK3,sK2) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_5251]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5263,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | l1_pre_topc(sK2) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2349,c_5252]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5349,plain,
% 48.04/6.50      ( v1_funct_1(X0_55) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,sK2,sK3) != iProver_top
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_5263,c_41,c_2883,c_3073,c_3075,c_3463]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5350,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),k2_pre_topc(sK2,X1_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),X0_55),X1_55))
% 48.04/6.50      | v1_funct_2(X0_55,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(X0_55,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(X0_55) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_5349]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5361,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55))
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_2344,c_5350]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5396,plain,
% 48.04/6.50      ( m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55)) ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_5361,c_45,c_46]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5397,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,X0_55)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),X0_55))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 48.04/6.50      inference(renaming,[status(thm)],[c_5396]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_5405,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_4543,c_5397]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_6422,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_6416,c_5405]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_15168,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 48.04/6.50      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | r1_tarski(k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))))),k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4)))))))) = iProver_top
% 48.04/6.50      | m1_subset_1(k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,k2_pre_topc(sK2,sK0(sK2,sK3,sK4))))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 48.04/6.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
% 48.04/6.50      | v1_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_6422,c_2360]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_15945,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5))
% 48.04/6.50      | v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
% 48.04/6.50      inference(global_propositional_subsumption,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_15168,c_38,c_41,c_35,c_44,c_34,c_45,c_33,c_46,c_32,
% 48.04/6.50                 c_47,c_50,c_129,c_130,c_1556,c_1662,c_1665,c_2900,
% 48.04/6.50                 c_2937,c_2940,c_2943,c_2959,c_3080,c_3083,c_3092,c_3152,
% 48.04/6.50                 c_3165,c_3232,c_3252,c_3328,c_3428,c_3600,c_3628,c_3754,
% 48.04/6.50                 c_3779,c_3780,c_4032,c_4800,c_4951,c_5405,c_5918,c_6180]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96459,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),sK5)) ),
% 48.04/6.50      inference(superposition,[status(thm)],[c_96447,c_15945]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96463,plain,
% 48.04/6.50      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4),k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 48.04/6.50      inference(demodulation,[status(thm)],[c_96458,c_96459]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_96467,plain,
% 48.04/6.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) = k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) ),
% 48.04/6.50      inference(light_normalisation,[status(thm)],[c_96457,c_96463]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_26,negated_conjecture,
% 48.04/6.50      ( ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) ),
% 48.04/6.50      inference(cnf_transformation,[],[f95]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_1560,negated_conjecture,
% 48.04/6.50      ( ~ v3_tops_2(sK4,sK2,sK3)
% 48.04/6.50      | ~ v2_funct_1(sK4)
% 48.04/6.50      | k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) ),
% 48.04/6.50      inference(subtyping,[status(esa)],[c_26]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_2338,plain,
% 48.04/6.50      ( k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK2)
% 48.04/6.50      | k2_struct_0(sK3) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4)
% 48.04/6.50      | k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(predicate_to_equality,[status(thm)],[c_1560]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3026,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k2_struct_0(sK2) != k2_struct_0(sK2)
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(demodulation,[status(thm)],[c_3023,c_2338]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(c_3037,plain,
% 48.04/6.50      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) != k2_struct_0(sK3)
% 48.04/6.50      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_pre_topc(sK2,sK5)) != k2_pre_topc(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5))
% 48.04/6.50      | v3_tops_2(sK4,sK2,sK3) != iProver_top
% 48.04/6.50      | v2_funct_1(sK4) != iProver_top ),
% 48.04/6.50      inference(equality_resolution_simp,[status(thm)],[c_3026]) ).
% 48.04/6.50  
% 48.04/6.50  cnf(contradiction,plain,
% 48.04/6.50      ( $false ),
% 48.04/6.50      inference(minisat,
% 48.04/6.50                [status(thm)],
% 48.04/6.50                [c_96467,c_96447,c_9944,c_4951,c_3921,c_3426,c_3037,
% 48.04/6.50                 c_2959,c_2943,c_2940,c_2937,c_47,c_46,c_45,c_44,c_41]) ).
% 48.04/6.50  
% 48.04/6.50  
% 48.04/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 48.04/6.50  
% 48.04/6.50  ------                               Statistics
% 48.04/6.50  
% 48.04/6.50  ------ General
% 48.04/6.50  
% 48.04/6.50  abstr_ref_over_cycles:                  0
% 48.04/6.50  abstr_ref_under_cycles:                 0
% 48.04/6.50  gc_basic_clause_elim:                   0
% 48.04/6.50  forced_gc_time:                         0
% 48.04/6.50  parsing_time:                           0.015
% 48.04/6.50  unif_index_cands_time:                  0.
% 48.04/6.50  unif_index_add_time:                    0.
% 48.04/6.50  orderings_time:                         0.
% 48.04/6.50  out_proof_time:                         0.088
% 48.04/6.50  total_time:                             5.952
% 48.04/6.50  num_of_symbols:                         63
% 48.04/6.50  num_of_terms:                           37764
% 48.04/6.50  
% 48.04/6.50  ------ Preprocessing
% 48.04/6.50  
% 48.04/6.50  num_of_splits:                          0
% 48.04/6.50  num_of_split_atoms:                     0
% 48.04/6.50  num_of_reused_defs:                     0
% 48.04/6.50  num_eq_ax_congr_red:                    42
% 48.04/6.50  num_of_sem_filtered_clauses:            1
% 48.04/6.50  num_of_subtypes:                        5
% 48.04/6.50  monotx_restored_types:                  0
% 48.04/6.50  sat_num_of_epr_types:                   0
% 48.04/6.50  sat_num_of_non_cyclic_types:            0
% 48.04/6.50  sat_guarded_non_collapsed_types:        0
% 48.04/6.50  num_pure_diseq_elim:                    0
% 48.04/6.50  simp_replaced_by:                       0
% 48.04/6.50  res_preprocessed:                       150
% 48.04/6.50  prep_upred:                             0
% 48.04/6.50  prep_unflattend:                        21
% 48.04/6.50  smt_new_axioms:                         0
% 48.04/6.50  pred_elim_cands:                        11
% 48.04/6.50  pred_elim:                              2
% 48.04/6.50  pred_elim_cl:                           -3
% 48.04/6.50  pred_elim_cycles:                       5
% 48.04/6.50  merged_defs:                            0
% 48.04/6.50  merged_defs_ncl:                        0
% 48.04/6.50  bin_hyper_res:                          0
% 48.04/6.50  prep_cycles:                            3
% 48.04/6.50  pred_elim_time:                         0.035
% 48.04/6.50  splitting_time:                         0.
% 48.04/6.50  sem_filter_time:                        0.
% 48.04/6.50  monotx_time:                            0.
% 48.04/6.50  subtype_inf_time:                       0.001
% 48.04/6.50  
% 48.04/6.50  ------ Problem properties
% 48.04/6.50  
% 48.04/6.50  clauses:                                40
% 48.04/6.50  conjectures:                            11
% 48.04/6.50  epr:                                    5
% 48.04/6.50  horn:                                   32
% 48.04/6.50  ground:                                 10
% 48.04/6.50  unary:                                  5
% 48.04/6.50  binary:                                 4
% 48.04/6.50  lits:                                   211
% 48.04/6.50  lits_eq:                                33
% 48.04/6.50  fd_pure:                                0
% 48.04/6.50  fd_pseudo:                              0
% 48.04/6.50  fd_cond:                                0
% 48.04/6.50  fd_pseudo_cond:                         0
% 48.04/6.50  ac_symbols:                             0
% 48.04/6.50  
% 48.04/6.50  ------ Propositional Solver
% 48.04/6.50  
% 48.04/6.50  prop_solver_calls:                      45
% 48.04/6.50  prop_fast_solver_calls:                 6614
% 48.04/6.50  smt_solver_calls:                       0
% 48.04/6.50  smt_fast_solver_calls:                  0
% 48.04/6.50  prop_num_of_clauses:                    22358
% 48.04/6.50  prop_preprocess_simplified:             35623
% 48.04/6.50  prop_fo_subsumed:                       608
% 48.04/6.50  prop_solver_time:                       0.
% 48.04/6.50  smt_solver_time:                        0.
% 48.04/6.50  smt_fast_solver_time:                   0.
% 48.04/6.50  prop_fast_solver_time:                  0.
% 48.04/6.50  prop_unsat_core_time:                   0.001
% 48.04/6.50  
% 48.04/6.50  ------ QBF
% 48.04/6.50  
% 48.04/6.50  qbf_q_res:                              0
% 48.04/6.50  qbf_num_tautologies:                    0
% 48.04/6.50  qbf_prep_cycles:                        0
% 48.04/6.50  
% 48.04/6.50  ------ BMC1
% 48.04/6.50  
% 48.04/6.50  bmc1_current_bound:                     -1
% 48.04/6.50  bmc1_last_solved_bound:                 -1
% 48.04/6.50  bmc1_unsat_core_size:                   -1
% 48.04/6.50  bmc1_unsat_core_parents_size:           -1
% 48.04/6.50  bmc1_merge_next_fun:                    0
% 48.04/6.50  bmc1_unsat_core_clauses_time:           0.
% 48.04/6.50  
% 48.04/6.50  ------ Instantiation
% 48.04/6.50  
% 48.04/6.50  inst_num_of_clauses:                    2789
% 48.04/6.50  inst_num_in_passive:                    539
% 48.04/6.50  inst_num_in_active:                     4223
% 48.04/6.50  inst_num_in_unprocessed:                846
% 48.04/6.50  inst_num_of_loops:                      4419
% 48.04/6.50  inst_num_of_learning_restarts:          1
% 48.04/6.50  inst_num_moves_active_passive:          176
% 48.04/6.50  inst_lit_activity:                      0
% 48.04/6.50  inst_lit_activity_moves:                2
% 48.04/6.50  inst_num_tautologies:                   0
% 48.04/6.50  inst_num_prop_implied:                  0
% 48.04/6.50  inst_num_existing_simplified:           0
% 48.04/6.50  inst_num_eq_res_simplified:             0
% 48.04/6.50  inst_num_child_elim:                    0
% 48.04/6.50  inst_num_of_dismatching_blockings:      6931
% 48.04/6.50  inst_num_of_non_proper_insts:           13657
% 48.04/6.50  inst_num_of_duplicates:                 0
% 48.04/6.50  inst_inst_num_from_inst_to_res:         0
% 48.04/6.50  inst_dismatching_checking_time:         0.
% 48.04/6.50  
% 48.04/6.50  ------ Resolution
% 48.04/6.50  
% 48.04/6.50  res_num_of_clauses:                     56
% 48.04/6.50  res_num_in_passive:                     56
% 48.04/6.50  res_num_in_active:                      0
% 48.04/6.50  res_num_of_loops:                       153
% 48.04/6.50  res_forward_subset_subsumed:            1621
% 48.04/6.50  res_backward_subset_subsumed:           10
% 48.04/6.50  res_forward_subsumed:                   0
% 48.04/6.50  res_backward_subsumed:                  0
% 48.04/6.50  res_forward_subsumption_resolution:     0
% 48.04/6.50  res_backward_subsumption_resolution:    0
% 48.04/6.50  res_clause_to_clause_subsumption:       27938
% 48.04/6.50  res_orphan_elimination:                 0
% 48.04/6.50  res_tautology_del:                      2303
% 48.04/6.50  res_num_eq_res_simplified:              0
% 48.04/6.50  res_num_sel_changes:                    0
% 48.04/6.50  res_moves_from_active_to_pass:          0
% 48.04/6.50  
% 48.04/6.50  ------ Superposition
% 48.04/6.50  
% 48.04/6.50  sup_time_total:                         0.
% 48.04/6.50  sup_time_generating:                    0.
% 48.04/6.50  sup_time_sim_full:                      0.
% 48.04/6.50  sup_time_sim_immed:                     0.
% 48.04/6.50  
% 48.04/6.50  sup_num_of_clauses:                     7080
% 48.04/6.50  sup_num_in_active:                      858
% 48.04/6.50  sup_num_in_passive:                     6222
% 48.04/6.50  sup_num_of_loops:                       882
% 48.04/6.50  sup_fw_superposition:                   4566
% 48.04/6.50  sup_bw_superposition:                   3340
% 48.04/6.50  sup_immediate_simplified:               180
% 48.04/6.50  sup_given_eliminated:                   0
% 48.04/6.50  comparisons_done:                       0
% 48.04/6.50  comparisons_avoided:                    96
% 48.04/6.50  
% 48.04/6.50  ------ Simplifications
% 48.04/6.50  
% 48.04/6.50  
% 48.04/6.50  sim_fw_subset_subsumed:                 142
% 48.04/6.50  sim_bw_subset_subsumed:                 307
% 48.04/6.50  sim_fw_subsumed:                        31
% 48.04/6.50  sim_bw_subsumed:                        0
% 48.04/6.50  sim_fw_subsumption_res:                 144
% 48.04/6.50  sim_bw_subsumption_res:                 0
% 48.04/6.50  sim_tautology_del:                      47
% 48.04/6.50  sim_eq_tautology_del:                   1
% 48.04/6.50  sim_eq_res_simp:                        4
% 48.04/6.50  sim_fw_demodulated:                     0
% 48.04/6.50  sim_bw_demodulated:                     6
% 48.04/6.50  sim_light_normalised:                   5
% 48.04/6.50  sim_joinable_taut:                      0
% 48.04/6.50  sim_joinable_simp:                      0
% 48.04/6.50  sim_ac_normalised:                      0
% 48.04/6.50  sim_smt_subsumption:                    0
% 48.04/6.50  
%------------------------------------------------------------------------------
