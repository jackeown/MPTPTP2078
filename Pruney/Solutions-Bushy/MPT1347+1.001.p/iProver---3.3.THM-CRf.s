%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:31 EST 2020

% Result     : Theorem 15.66s
% Output     : CNFRefutation 15.66s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_31061)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( v4_pre_topc(X3,X0)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( v4_pre_topc(X3,X0)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f60])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4),X1)
          | ~ v4_pre_topc(sK4,X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4),X1)
          | v4_pre_topc(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0) )
                & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | v4_pre_topc(X3,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_funct_1(X2)
            | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | ~ v3_tops_2(X2,X0,X1) )
          & ( ( ! [X4] :
                  ( ( ( v4_pre_topc(X4,X0)
                      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                      | ~ v4_pre_topc(X4,X0) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
            | v3_tops_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X3),X1)
                | ~ v4_pre_topc(X3,X0) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X3),X1)
                | v4_pre_topc(X3,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_funct_1(sK3)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3)
          | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3)
          | ~ v3_tops_2(sK3,X0,X1) )
        & ( ( ! [X4] :
                ( ( ( v4_pre_topc(X4,X0)
                    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),X1) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),X1)
                    | ~ v4_pre_topc(X4,X0) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & v2_funct_1(sK3)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3)
            & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) )
          | v3_tops_2(sK3,X0,X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X3),sK2)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X3),sK2)
                    | v4_pre_topc(X3,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2)
              | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2)
              | ~ v3_tops_2(X2,X0,sK2) )
            & ( ( ! [X4] :
                    ( ( ( v4_pre_topc(X4,X0)
                        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X4),sK2) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,X4),sK2)
                        | ~ v4_pre_topc(X4,X0) ) )
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2)
                & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) )
              | v3_tops_2(X2,X0,sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,sK1) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,sK1) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
                | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
                | ~ v3_tops_2(X2,sK1,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,sK1)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,sK1) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
                  & k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) )
                | v3_tops_2(X2,sK1,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
          | ~ v4_pre_topc(sK4,sK1) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
          | v4_pre_topc(sK4,sK1) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_funct_1(sK3)
      | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      | ~ v3_tops_2(sK3,sK1,sK2) )
    & ( ( ! [X4] :
            ( ( ( v4_pre_topc(X4,sK1)
                | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4),sK2) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4),sK2)
                | ~ v4_pre_topc(X4,sK1) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & v2_funct_1(sK3)
        & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
        & k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) )
      | v3_tops_2(sK3,sK1,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f61,f65,f64,f63,f62])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f105,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f106,plain,
    ( v2_funct_1(sK3)
    | v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f107,plain,(
    ! [X4] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4),sK2)
      | ~ v4_pre_topc(X4,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_tops_2(sK3,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,
    ( k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | ~ v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,(
    ! [X4] :
      ( v4_pre_topc(X4,sK1)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X4),sK2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_tops_2(sK3,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f110,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | ~ v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | ~ v3_tops_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3330,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2))) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6662,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3315,c_3330])).

cnf(c_44,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_46,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_48,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6888,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6662,c_45,c_46,c_47,c_48])).

cnf(c_6889,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6888])).

cnf(c_31,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3316,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6892,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK0(sK1,sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6889,c_3316])).

cnf(c_3312,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_21,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_590,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_21,c_8])).

cnf(c_3310,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_7422,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3312,c_3310])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3322,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4433,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3315,c_3322])).

cnf(c_14,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,negated_conjecture,
    ( v3_tops_2(sK3,sK1,sK2)
    | k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1456,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_38])).

cnf(c_1457,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1456])).

cnf(c_1459,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1457,c_44,c_43,c_42,c_41,c_40])).

cnf(c_4434,plain,
    ( k2_relat_1(sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4433,c_1459])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3318,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5886,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4434,c_3318])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3482,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3482])).

cnf(c_3625,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3624])).

cnf(c_6150,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5886,c_47,c_49,c_3625])).

cnf(c_7425,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7422,c_6150])).

cnf(c_7928,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = sK0(sK1,sK2,sK3)
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6892,c_7425])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,negated_conjecture,
    ( v3_tops_2(sK3,sK1,sK2)
    | v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1504,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_funct_1(X0)
    | v2_funct_1(sK3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_37])).

cnf(c_1505,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1504])).

cnf(c_1507,plain,
    ( v2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1505,c_44,c_43,c_42,c_41,c_40])).

cnf(c_1765,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1507])).

cnf(c_1766,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1
    | k2_tops_2(X0,X1,sK3) = k2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_1770,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK3,X0,X1)
    | k2_relset_1(X0,X1,sK3) != X1
    | k2_tops_2(X0,X1,sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_42])).

cnf(c_1771,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK3) != X1
    | k2_tops_2(X0,X1,sK3) = k2_funct_1(sK3) ),
    inference(renaming,[status(thm)],[c_1770])).

cnf(c_3290,plain,
    ( k2_relset_1(X0,X1,sK3) != X1
    | k2_tops_2(X0,X1,sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,X0,X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1771])).

cnf(c_3686,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_struct_0(sK2) != u1_struct_0(sK2)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_3290])).

cnf(c_3687,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3686])).

cnf(c_3940,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | k2_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3686,c_41,c_40,c_3687])).

cnf(c_7427,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_7422,c_3940])).

cnf(c_7429,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_7427])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3328,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8479,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7429,c_3328])).

cnf(c_37460,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8479,c_47,c_48,c_49])).

cnf(c_37467,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,k2_funct_1(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37460,c_3330])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3326,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5900,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3315,c_3326])).

cnf(c_4580,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5733,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4580])).

cnf(c_5734,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5733])).

cnf(c_6145,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5900,c_47,c_48,c_49,c_5734])).

cnf(c_8472,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7429,c_6145])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3327,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8480,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7429,c_3327])).

cnf(c_46802,plain,
    ( m1_subset_1(sK0(sK2,sK1,k2_funct_1(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37467,c_45,c_46,c_47,c_48,c_49,c_8472,c_8480])).

cnf(c_46803,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | m1_subset_1(sK0(sK2,sK1,k2_funct_1(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_46802])).

cnf(c_46806,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | r1_tarski(sK0(sK2,sK1,k2_funct_1(sK3)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46803,c_3316])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3317,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3321,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4994,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3315,c_3321])).

cnf(c_11,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( v3_tops_2(sK3,sK1,sK2)
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1609,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v4_pre_topc(X3,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_1610,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1609])).

cnf(c_1614,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_44,c_43,c_42,c_41,c_40])).

cnf(c_3294,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1614])).

cnf(c_5277,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4994,c_3294])).

cnf(c_8276,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5277,c_7429])).

cnf(c_8282,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_8276])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3320,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6024,plain,
    ( k8_relset_1(X0,X1,k2_tops_2(X1,X0,X2),X3) = k10_relat_1(k2_tops_2(X1,X0,X2),X3)
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3328,c_3320])).

cnf(c_27621,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),X0) = k10_relat_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3315,c_6024])).

cnf(c_29,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1729,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1507])).

cnf(c_1730,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_1729])).

cnf(c_1734,plain,
    ( ~ v1_relat_1(sK3)
    | k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1730,c_42])).

cnf(c_3292,plain,
    ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_4193,plain,
    ( k10_relat_1(k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_42,c_40,c_1730,c_3624])).

cnf(c_27626,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27621,c_4193,c_7429])).

cnf(c_28055,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_funct_1(sK3),X0) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27626,c_47,c_48])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3332,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28058,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK0(sK2,sK1,k2_funct_1(sK3))),sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28055,c_3332])).

cnf(c_28186,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK0(sK2,sK1,k2_funct_1(sK3))),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28058,c_45,c_46,c_47,c_48,c_49,c_8472,c_8479,c_8480])).

cnf(c_28191,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(sK0(sK2,sK1,k2_funct_1(sK3)),sK1) != iProver_top
    | r1_tarski(sK0(sK2,sK1,k2_funct_1(sK3)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8282,c_28186])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3331,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) = iProver_top
    | v4_pre_topc(sK0(X1,X2,X0),X2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_37468,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | v4_pre_topc(sK0(sK2,sK1,k2_funct_1(sK3)),sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_37460,c_3331])).

cnf(c_38538,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top
    | r1_tarski(sK0(sK2,sK1,k2_funct_1(sK3)),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28191,c_45,c_46,c_47,c_48,c_49,c_8472,c_8480,c_31061])).

cnf(c_47032,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46806,c_38538])).

cnf(c_15,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,negated_conjecture,
    ( v3_tops_2(sK3,sK1,sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1408,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) = k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_39])).

cnf(c_1409,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1408])).

cnf(c_1411,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1409,c_44,c_43,c_42,c_41,c_40])).

cnf(c_10,plain,
    ( v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( ~ v3_tops_2(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1324,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_34])).

cnf(c_1325,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1324])).

cnf(c_1327,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1325,c_44,c_43,c_42,c_41,c_40])).

cnf(c_1328,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1327])).

cnf(c_1422,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1411,c_1328])).

cnf(c_1466,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1459,c_1422])).

cnf(c_1514,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1507,c_1466])).

cnf(c_3309,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_8474,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7429,c_3309])).

cnf(c_47037,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_47032,c_8474])).

cnf(c_47999,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_47037,c_3316])).

cnf(c_48139,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = sK0(sK1,sK2,sK3)
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7928,c_47999])).

cnf(c_26,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3319,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1747,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1507])).

cnf(c_1748,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1747])).

cnf(c_1752,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1748,c_42])).

cnf(c_3291,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_1749,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1748])).

cnf(c_4354,plain,
    ( r1_tarski(k10_relat_1(sK3,k9_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_47,c_49,c_1749,c_3625])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3334,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4482,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k10_relat_1(sK3,k9_relat_1(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4354,c_3334])).

cnf(c_9065,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3319,c_4482])).

cnf(c_3311,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7423,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3311,c_3310])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3323,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4440,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3315,c_3323])).

cnf(c_4441,plain,
    ( k1_relat_1(sK3) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_4440,c_1411])).

cnf(c_7539,plain,
    ( k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_7423,c_4441])).

cnf(c_9072,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9065,c_7539])).

cnf(c_9098,plain,
    ( r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9072,c_49,c_3625])).

cnf(c_9099,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9098])).

cnf(c_48973,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = sK0(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_48139,c_9099])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5302,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4994,c_3325])).

cnf(c_5533,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5302,c_49])).

cnf(c_48988,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | m1_subset_1(sK0(sK1,sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_48973,c_5533])).

cnf(c_4489,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3315,c_3320])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3329,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v5_pre_topc(X0,X1,X2) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6782,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_3329])).

cnf(c_6988,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6782,c_45,c_46,c_47,c_48,c_49])).

cnf(c_49132,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_48988,c_6988])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5092,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_3324])).

cnf(c_5522,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5092,c_49])).

cnf(c_12,plain,
    ( ~ v3_tops_2(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( v3_tops_2(sK3,sK1,sK2)
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1579,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | v4_pre_topc(X3,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_1580,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1579])).

cnf(c_1584,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_44,c_43,c_42,c_41,c_40])).

cnf(c_3295,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1584])).

cnf(c_5280,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4994,c_3295])).

cnf(c_7103,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,k10_relat_1(sK3,X0)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_5280])).

cnf(c_48991,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_48973,c_7103])).

cnf(c_49135,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49132,c_48991])).

cnf(c_6677,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_3332])).

cnf(c_6895,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6677,c_45,c_46,c_47,c_48,c_49])).

cnf(c_49139,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_49135,c_6895])).

cnf(c_6497,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3315,c_3331])).

cnf(c_6788,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK3),sK2) = iProver_top
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6497,c_45,c_46,c_47,c_48])).

cnf(c_6789,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK0(sK1,sK2,sK3),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6788])).

cnf(c_49234,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49139,c_45,c_46,c_47,c_48,c_49,c_5813,c_6677,c_48991])).

cnf(c_49235,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | v5_pre_topc(sK3,sK1,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_49234])).

cnf(c_49239,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49235,c_47999])).

cnf(c_50875,plain,
    ( k10_relat_1(sK3,k9_relat_1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_49239,c_9099])).

cnf(c_51061,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_50875,c_5522])).

cnf(c_33,negated_conjecture,
    ( ~ v3_tops_2(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1266,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_35,c_33])).

cnf(c_1420,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1411,c_1266])).

cnf(c_1468,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1459,c_1420])).

cnf(c_1521,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1507,c_1468])).

cnf(c_2287,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1521])).

cnf(c_3299,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2287])).

cnf(c_4989,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3299,c_3295])).

cnf(c_1555,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ v4_pre_topc(X3,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_36])).

cnf(c_1556,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_1555])).

cnf(c_1560,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1556,c_44,c_43,c_42,c_41,c_40])).

cnf(c_3296,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_32,negated_conjecture,
    ( ~ v3_tops_2(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1295,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_35,c_32])).

cnf(c_1421,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1411,c_1295])).

cnf(c_1467,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_funct_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1459,c_1421])).

cnf(c_1522,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1507,c_1467])).

cnf(c_2286,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1522])).

cnf(c_3297,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2286])).

cnf(c_4362,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3296,c_3297])).

cnf(c_6244,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4989,c_4362])).

cnf(c_51075,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_51061,c_6244])).

cnf(c_6248,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_6244])).

cnf(c_28059,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28055,c_3329])).

cnf(c_28197,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28059,c_45,c_46,c_47,c_48,c_49,c_8276,c_8472,c_8479,c_8480])).

cnf(c_28205,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_28197])).

cnf(c_5274,plain,
    ( v4_pre_topc(k9_relat_1(sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_4994,c_3297])).

cnf(c_28647,plain,
    ( v4_pre_topc(sK4,sK1) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_28205,c_5274])).

cnf(c_1350,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_1351,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1350])).

cnf(c_1353,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_44,c_43,c_42,c_41,c_40])).

cnf(c_1354,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1353])).

cnf(c_1423,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1411,c_1354])).

cnf(c_1465,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1459,c_1423])).

cnf(c_1515,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | v4_pre_topc(sK4,sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1507,c_1465])).

cnf(c_3308,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_7932,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3308,c_7429])).

cnf(c_7933,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7932,c_4994])).

cnf(c_47038,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) = iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_47032,c_7933])).

cnf(c_1379,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0),X2,X1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_1380,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1379])).

cnf(c_1382,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1380,c_44,c_43,c_42,c_41,c_40])).

cnf(c_1383,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1382])).

cnf(c_1424,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1411,c_1383])).

cnf(c_1464,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1459,c_1424])).

cnf(c_1516,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1)
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v4_pre_topc(sK4,sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1507,c_1464])).

cnf(c_3307,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_5817,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3307,c_4994])).

cnf(c_8473,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7429,c_5817])).

cnf(c_28646,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28205,c_8473])).

cnf(c_3537,plain,
    ( r1_tarski(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_33598,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3537])).

cnf(c_33606,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33598])).

cnf(c_38543,plain,
    ( v4_pre_topc(sK4,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28646,c_8474,c_33606])).

cnf(c_38544,plain,
    ( v5_pre_topc(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_38543])).

cnf(c_47452,plain,
    ( v4_pre_topc(k9_relat_1(sK3,sK4),sK2) = iProver_top
    | v5_pre_topc(sK3,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47038,c_7933,c_38538,c_38544,c_46806])).

cnf(c_47453,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_47452])).

cnf(c_5539,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5533,c_3316])).

cnf(c_7927,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,k9_relat_1(sK3,X0))) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_5539,c_7425])).

cnf(c_2285,plain,
    ( v4_pre_topc(X0,sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1522])).

cnf(c_3298,plain,
    ( v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_5276,plain,
    ( v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_4994,c_3298])).

cnf(c_5671,plain,
    ( v4_pre_topc(k10_relat_1(sK3,X0),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,k10_relat_1(sK3,X0)),sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_5276])).

cnf(c_9775,plain,
    ( v4_pre_topc(k10_relat_1(sK3,k9_relat_1(sK3,X0)),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_7927,c_5671])).

cnf(c_6998,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k9_relat_1(sK3,X0)),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5533,c_6988])).

cnf(c_16507,plain,
    ( v5_pre_topc(sK3,sK1,sK2) = iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k9_relat_1(sK3,X0)),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7927,c_7103])).

cnf(c_22627,plain,
    ( v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,k9_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9775,c_6998,c_16507])).

cnf(c_22628,plain,
    ( v4_pre_topc(k10_relat_1(sK3,k9_relat_1(sK3,X0)),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_22627])).

cnf(c_51053,plain,
    ( v4_pre_topc(k9_relat_1(sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_50875,c_22628])).

cnf(c_5528,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5522,c_3316])).

cnf(c_51060,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_50875,c_5528])).

cnf(c_51248,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51075,c_6248,c_28647,c_47453,c_51053,c_51060])).

cnf(c_48006,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(k9_relat_1(sK3,sK4),sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_47037,c_5276])).

cnf(c_47036,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_47032,c_38544])).

cnf(c_5670,plain,
    ( v4_pre_topc(X0,sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,X0),sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_5276])).

cnf(c_47460,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | v4_pre_topc(sK4,sK1) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_47453,c_5670])).

cnf(c_48757,plain,
    ( v5_pre_topc(sK3,sK1,sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48006,c_8474,c_28646,c_33606,c_38538,c_46806,c_47460,c_47999])).

cnf(c_48761,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = sK0(sK1,sK2,sK3)
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_7928,c_48757])).

cnf(c_51252,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))) = sK0(sK1,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_51248,c_48761])).

cnf(c_51557,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top
    | v4_pre_topc(k9_relat_1(sK3,k10_relat_1(sK3,sK0(sK1,sK2,sK3))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_51252,c_22628])).

cnf(c_51569,plain,
    ( v4_pre_topc(sK0(sK1,sK2,sK3),sK2) != iProver_top
    | v4_pre_topc(k10_relat_1(sK3,sK0(sK1,sK2,sK3)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_51557,c_51252])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51569,c_51248,c_48757,c_6895,c_6789])).


%------------------------------------------------------------------------------
